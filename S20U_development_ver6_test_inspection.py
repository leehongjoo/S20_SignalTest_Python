from PySide2.QtWidgets import (QMainWindow, QAction, QApplication, QSplashScreen, QDockWidget, QListWidget,
                               QProgressBar, QLabel, QMessageBox, QWidget, QVBoxLayout, QHBoxLayout, QPushButton,
                               QTableWidget, QAbstractItemView, QTableWidgetItem, QActionGroup)
from PySide2.QtGui import QIcon, QPixmap
from PySide2.QtCore import Qt, QRect
import os
import PySide2
import pyqtgraph as pg
# from screeninfo import get_monitors
import pyqtgraph.opengl as gl
from scipy import fftpack
from scipy.integrate import simps
import stopdialog
import quamash
import asyncio
import numpy as np
from collections import deque, Counter
import enum
import two_com as tc
import lowpass_filter as lf
import notch_filter as nf
import highpass_filter as hf
import band_pass_filter as bf
import matplotlib.pyplot as plt
import xml.etree.ElementTree as ET
import xml_write
# import fft_xml_write
import datetime
from time import time
from bleak import BleakScanner
from bleak import BleakClient
import sys

irName = os.path.dirname(PySide2.__file__)
plugin_path = os.path.join(dirName, 'plugins', 'platforms')
os.environ['QT_QPA_PLATFORM_PLUGIN_PATH'] = plugin_path


class MainWindow(QMainWindow):
    def __init__(self, parent=None):
        super(MainWindow, self).__init__(parent)
        # const value
        self.yRange = [-20, 20]
        self.dequeMax = 250
        self.fftMax = 250
        self.offset = 1
        self.notchCutOff = 60
        self.notchQualityFactor = 30
        self.lowPassCutOff = 50
        self.lowPassOrder = 5
        self.BL = 250
        self.frequencyRange = 50
        self.samplingRate = 250
        self.two_16 = pow(2, 16)
        self.two_8 = pow(2, 8)
        self.max_uv = 2.7
        self.two_resolution = 8388607
        self.rawGraphFrame = 25
        self.update_num = 10
        self.windowed = np.hamming(self.fftMax)
        self.fftHeight = 5

        #ble_battery algorism
        self.battery_array = deque(np.zeros(0), maxlen=5)
        self.battery_array.append(75)
        self.battery_array.append(75)
        self.battery_array.append(75)
        # value
        self.timerCounter = 0
        self.printIndex = 0
        self.printIndex2 = 0
        self.fftIndex = 0
        self.ch1_1_value = 0
        self.ch1_2_value = 0
        self.ch1_3_value = 0
        self.ch2_1_value = 0
        self.ch2_2_value = 0
        self.ch2_3_value = 0
        self.dataIndex = 0
        self.USB_Plug_Count = 0
        self.boolFirstStart = False
        self.boolPaused = True
        self.pwrBtnStr = "Pwr :"
        self.boolPower = False
        self.boolBLELED = False
        self.boolConnectAttempt = False
        self.screenHeight = 1000
        self.screenWidth = 1920
        self.notchSelect = notchFilterSelect.notch60
        self.lowPassSelect = lowPassFilterSelect.bpf2_50
        self.FFT_Select = FFT_Channel_Select.ch1

        fft_freq = fftpack.fftfreq(self.BL, 1 / self.samplingRate)
        pos_mask = np.where(fft_freq > 0)
        self.frequencies = fft_freq[pos_mask]
        self.frequencies = self.frequencies[:60]  # np.delete(self.frequencies, range(50, 250))

        # UI
        self.pgWidget = QWidget()
        self.setCentralWidget(self.pgWidget)
        self.setGeometry(QRect(0, 0, self.screenWidth, self.screenHeight))

        self.dockingWidget = QDockWidget("개발용 data 보드")
        self.listWidget = QListWidget()
        self.listWidget.setFont("consolas")
        self.dockingWidget.setWidget(self.listWidget)
        self.dockingWidget.setAllowedAreas(Qt.LeftDockWidgetArea | Qt.RightDockWidgetArea)
        self.dockingWidget.setFloating(False)
        self.addDockWidget(Qt.RightDockWidgetArea, self.dockingWidget)
        '''
        self.dockingWidget2 = QDockWidget("개발용 log 보드")
        self.listWidget2 = QListWidget()
        self.listWidget2.setFont("consolas")
        self.dockingWidget2.setWidget(self.listWidget2)
        self.dockingWidget2.setAllowedAreas(Qt.TopDockWidgetArea | Qt.BottomDockWidgetArea)
        self.dockingWidget2.setFloating(False)
        self.addDockWidget(Qt.BottomDockWidgetArea, self.dockingWidget2)
        '''
        self.tableWidgetScan = QTableWidget()
        self.tableWidgetScan.itemClicked.connect(self.connectEnable)
        self.tableWidgetScan.itemDoubleClicked.connect(self.connectAddress)
        self.tableWidgetScan.setSelectionMode(QAbstractItemView.SingleSelection)
        self.tableWidgetScan.setEditTriggers(QAbstractItemView.NoEditTriggers)

        self.lLabel = QLabel("처음은 Scan 버튼을 누르세요.")
        self.lLabel.resize(150, 45)
        self.lLabel.setMaximumHeight(45)
        self.lLabel.setMinimumHeight(40)
        self.lLabel.setStyleSheet("color: blue;"
                                  "border-style: solid;"
                                  "border-width: 1px;"
                                  "border-color: #c1f7fe;"
                                  "border-radius: 3px;"
                                  "background-color: #F7FFFE;")
        font1 = self.lLabel.font()
        font1.setPointSize(25)
        font1.setFamily('consolas')
        font1.setBold(True)
        self.lLabel.setFont(font1)

        self.lLabel_battery = QLabel("0h 0m 0s: MSB=  , Bat= ")
        self.lLabel_battery.resize(30, 45)
        self.lLabel_battery.setMaximumHeight(45)
        self.lLabel_battery.setMinimumHeight(40)
        self.lLabel_battery.setStyleSheet("color: blue;"
                                          "border-style: solid;"
                                          "border-width: 1px;"
                                          "border-color: #c1f7fe;"
                                          "border-radius: 3px;"
                                          "background-color: #F7FFFE;")
        font1 = self.lLabel_battery.font()
        font1.setPointSize(25)
        font1.setFamily('consolas')
        font1.setBold(True)
        self.lLabel_battery.setFont(font1)

        self.setWindowTitle('Brint Monitor')
        self.setWindowIcon(QIcon("./images/brainGreen.png"))

        self.vBoxLayout = QVBoxLayout(self.pgWidget)
        self.vBoxLayoutPG = QVBoxLayout()
        self.hBoxLayoutLabel = QHBoxLayout()

        self.vBoxLayout.addLayout(self.vBoxLayoutPG)

        # table
        self.tableWidgetScan.setColumnCount(3)
        self.tableWidgetScan.setColumnWidth(0, 180)
        self.tableWidgetScan.setColumnWidth(1, 300)
        self.tableWidgetScan.setRowCount(3)
        self.tableWidgetScan.setHorizontalHeaderLabels(["Name", "Address", "Rssi"])
        self.tableWidgetScan.setSelectionBehavior(QAbstractItemView.SelectRows)  # multiple row select

        # graph
        '''
        self.ax_fft = pg.PlotWidget()
        self.ax_fft.setMaximumHeight(340)
        self.ax_fft.setMinimumHeight(150)
        self.ax_fft.setTitle("FFT", color=(0, 0, 0))
        self.ax_fft.setLabel('left', "Amplitude", color='white')
        self.ax_fft.setLabel('bottom', "Frequency(Hz)", color='white')
        self.ax_fft.setRange(xRange=[0, 60], disableAutoRange=True)
        self.ax_fft.showGrid(True, True, alpha=1.0)
        self.vBoxLayoutPG.addWidget(self.ax_fft)
        '''

        # 3d graph
        '''
        self.ax_3d = gl.GLViewWidget()
        self.ax_3d.setMaximumHeight(800)
        self.ax_3d.setMinimumHeight(650)
        self.ax_3d.setCameraPosition(distance=120, azimuth=55, elevation=30)
        self.gz = gl.GLGridItem()
        self.gz.setDepthValue(10)
        self.gz.rotate(90, 0, 1, 0)
        # self.gz.scale(1,1,1)
        self.gz.setSize(50, 120, 1)
        self.gz.translate(-20, 0, 25)
        self.gx = gl.GLGridItem()
        self.gx.setSize(50, 120, 1)
        self.gx.translate(5, 0, 0)
        self.ax_3d.addItem(self.gz)
        self.ax_3d.addItem(self.gx)
        #self.vBoxScanBarFFtLayout.addWidget(self.ax_3d)
        self.cMap = plt.get_cmap('jet')
        self.freq_ix = dict()
        self.freqBand = dict()
        self.ampBand = dict()
        self.Time = dict()
        self.Fre = dict()
        self.CvMax = dict()
        self.surfPlot = dict()

        for band in eeg_bands:
            self.freq_ix[band] = np.where((self.frequencies >= eeg_bands[band][0])
                                          & (self.frequencies <= eeg_bands[band][1]))[0]
            self.freqBand[band] = self.frequencies[self.freq_ix[band]]
            self.ampBand[band] = np.zeros((len(self.freq_ix[band]), 120))
            self.Time[band] = np.linspace(0, 119, 120)
            self.Fre[band] = self.freqBand[band]
            self.cMap = plt.get_cmap(cMapList[band])
            self.CvMax[band] = self.cMap(self.ampBand[band] / self.fftHeight)
            self.surfPlot[band] = gl.GLSurfacePlotItem(x=self.Fre[band], y=self.Time[band], z=self.ampBand[band],
                                                       colors=self.CvMax[band], smooth=True)
            self.ax_3d.addItem(self.surfPlot[band])
        self.surfPlot['Delta'].translate(-20, -60, 0)
        self.surfPlot['Theta'].translate(-20.5, -60, 0)
        self.surfPlot['Alpha'].translate(-21, -60, 0)
        self.surfPlot['Beta'].translate(-21.5, -60, 0)
        self.surfPlot['Gamma'].translate(-22, -60, 0)

        #self.vBoxScanBarFFtLayout.addWidget(self.tableWidgetScan)
        '''