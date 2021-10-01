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
        self.ax1 = pg.PlotWidget()
        self.ax1.setMaximumHeight(400)
        self.ax1.setMinimumHeight(150)
        self.ax1.setDownsampling(mode='peak')
        self.ax1.setLabel('left', "Left", color='blue')
        self.ax1.setClipToView(True)
        self.ax1.setRange(xRange=[-5, 0], yRange=[-100, 100])
        #self.ax1.setXRange(-4, 0)
        self.ax1.showGrid(True, True, alpha=1.0)
        '''
        self.ax2 = pg.PlotWidget()
        self.ax2.setMaximumHeight(340)
        self.ax2.setMinimumHeight(150)
        self.ax2.setDownsampling(mode='peak')
        self.ax2.setLabel('left', "Alpha", color='blue')
        self.ax2.setClipToView(True)
        self.ax2.setRange(xRange=[-4, 0], yRange=[-50, 50])  # disableAutoRange=False
        self.ax2.setXRange(-4, 0)
        self.ax2.showGrid(True, True, alpha=1.0)
        '''
        self.ax3 = pg.PlotWidget()
        self.ax3.setMaximumHeight(400)
        self.ax3.setMinimumHeight(150)
        self.ax3.setDownsampling(mode='peak')
        self.ax3.setLabel('left', "Right", color='red')
        self.ax3.setClipToView(True)
        self.ax3.setRange(xRange=[-5, 0], yRange=[-100, 100])
        #self.ax3.setXRange(-4, 0)
        self.ax3.showGrid(True, True, alpha=1.0)
        '''
        self.ax4 = pg.PlotWidget()
        self.ax4.setMaximumHeight(340)
        self.ax4.setMinimumHeight(150)
        self.ax4.setDownsampling(mode='peak')
        self.ax4.setLabel('left', "Alpha", color='red')
        self.ax4.setClipToView(True)
        self.ax4.setRange(xRange=[-4, 0], yRange=[-50, 50])
        self.ax4.setXRange(-4, 0)
        self.ax4.showGrid(True, True, alpha=1.0)
        '''
        self.vBoxLayoutPG.addWidget(self.ax1)
        #self.vBoxLayoutPG.addWidget(self.ax2)
        self.vBoxLayoutPG.addWidget(self.ax3)
        #self.vBoxLayoutPG.addWidget(self.ax4)
        self.pen_brown = pg.mkPen(color=(141, 110, 99))
        self.pen_red = pg.mkPen(color=(244, 67, 54))
        self.pen_orange = pg.mkPen(color=(255, 87, 34))
        self.pen_green = pg.mkPen(color=(76, 175, 80))
        self.pen_blue = pg.mkPen(color=(76, 175, 243))
        self.pen_violet = pg.mkPen(color=(224, 64, 251))
        self.pen_gray = pg.mkPen(color=(213, 213, 213))
        self.line1 = self.ax1.plot(pen=self.pen_blue)
        self.line2 = self.ax3.plot(pen=self.pen_red)
        #self.line3 = self.ax2.plot(pen=self.pen_green)
        #self.line4 = self.ax4.plot(pen=self.pen_orange)
        #self.line_fft = self.ax_fft.plot(pen=self.pen_blue)
        #self.line_fft_ch2 = self.ax_fft.plot(pen=self.pen_red)
        self.data1 = np.zeros(30000)
        self.data2 = np.zeros(30000)
        self.data3 = np.zeros(30000)
        self.data1_x = np.linspace(0, 29999, 30000) * 0.004
        self.data2_x = np.linspace(0, 29999, 30000) * 0.004
        self.data3_x = np.linspace(0, 29999, 30000) * 0.004
        self.data4 = np.zeros(30000)
        self.data4_x = np.linspace(0, 29999, 30000) * 0.004
        #self.data_fft = np.zeros(50)
        #self.data_fft_x = np.linspace(0, 49, 50)
        #self.data_fft_ch2 = np.zeros(50)
        #self.data_fft_ch2_x = np.linspace(0, 49, 50)
        self.vBoxLayoutPG.addLayout(self.hBoxLayoutLabel)
        self.hBoxLayoutLabel.addWidget(self.lLabel)
        self.hBoxLayoutLabel.addWidget(self.lLabel_battery)
        self.vBoxLayoutPG.addWidget(self.tableWidgetScan)

        # database
        self.fData = deque(np.zeros(self.dequeMax), maxlen=self.dequeMax)
        self.fData2 = deque(np.zeros(self.dequeMax), maxlen=self.dequeMax)
        self.fData3 = deque(np.zeros(self.fftMax), maxlen=self.fftMax)
        self.fData4 = deque(np.zeros(self.fftMax), maxlen=self.fftMax)
        self.bufferLeft = []
        self.bufferRight = []
        self.ch1_int_buffer = []
        self.ch2_int_buffer = []

        # xml
        self.user = ET.Element("userName")

        # bluetooth
        self.scanner = BleakScanner()
        self.macAddress = ""
        self.Read_UUID = "0000fff6-0000-1000-8000-00805f9b34fb"
        self.Write_UUID = "0000fff1-0000-1000-8000-00805f9b34fb"
        self.Power_UUID = "0000fff3-0000-1000-8000-00805f9b34fb"
        self.BLE_UUID = "0000fff3-0000-1000-8000-00805f9b34fb"
        self.USB_Plug_UUID = "0000fff4-0000-1000-8000-00805f9b34fb"
        self.HwVersion_UUID = "00002a26-0000-1000-8000-00805f9b34fb"
        self.client = None
        self.element = [37]
        self.byteWrite = bytearray(self.element)
        self.byteLED = 2
        self.strPanaxtos = "Panaxtos"
        self.panaxAddress = ""
        self.find_device = False
        self.noexcept = False
        self.conBool = False
        self.HwVersion = ""

        # event
        # create actions, file menu action
        self.save = QAction("&Save", self)
        self.save.setIcon(QIcon("./images/saveBlue2.png"))
        self.save.setShortcut("Ctrl+S")
        self.save.setStatusTip("Save .xml file")
        self.save.triggered.connect(self.save_xml)
        self.save.setDisabled(True)
        self.exitAction = QAction("E&xit", self)
        self.exitAction.setShortcut("Ctrl+Q")
        self.exitAction.setStatusTip("Exit the application")
        self.exitAction.triggered.connect(self.close)
        self.scan = QAction("&Scan", self)
        self.scan.setIcon(QIcon("./images/scanBlue.png"))
        self.scan.triggered.connect(self.autoScan)
        self.connection = QAction("&Connect", self)
        self.connection.setIcon(QIcon("./images/connectBlue.png"))
        self.connection.triggered.connect(self.connectAddress)
        self.connection.setDisabled(True)
        #self.disconnection = QAction("D&isconnect", self)
        #self.disconnection.setIcon(QIcon("./images/disconnected.png"))
        #self.disconnection.triggered.connect(self.disconnectAddress)
        #self.disconnection.setDisabled(True)
        self.stop = QAction("&Disconnect", self)
        self.stop.setIcon(QIcon("./images/disconnected2.png"))
        self.stop.setStatusTip("측정을 멈춤니다")
        self.stop.triggered.connect(self.stopDialog)
        self.stop.setDisabled(True)
        self.paused = QAction("P&ause", self)
        self.paused.setIcon(QIcon("./images/playBlue2.png"))
        self.paused.setStatusTip("측정을 정지합니다")
        self.paused.triggered.connect(self.startMeasureBtn)
        self.paused.setDisabled(True)

        # LED menu
        self.powerLED = QAction("&Power", self)
        self.powerLED.setIcon(QIcon("./images/pwrLED.png"))
        self.powerLED.setStatusTip("Power LED On/Off")
        self.powerLED.triggered.connect(self.powerLEDOnOff)
        self.powerLED.setDisabled(True)
        self.BLELED = QAction("&BLE", self)
        self.BLELED.setIcon(QIcon("./images/BLE.png"))
        self.BLELED.setStatusTip("BLE LED On/Off")
        self.BLELED.triggered.connect(self.BLELEDOnOff)
        self.BLELED.setDisabled(True)
        # additional function
        self.USB_Plug = QAction("&USB_Plug", self)
        self.USB_Plug.setIcon(QIcon("./images/pwrBtnPurple.png"))
        self.USB_Plug.triggered.connect(self.USB_PlugConfirmButton)
        self.USB_Plug.setDisabled(True)
        self.HwVersionConfirm = QAction("&Hw", self)
        self.HwVersionConfirm.setStatusTip("USB Plug Confirm")
        self.HwVersionConfirm.triggered.connect(self.HwVersionConfirmButton)
        self.HwVersionConfirm.setDisabled(True)

        # notch & lowpass filter
        self.notch60 = QAction("60Hz", self)
        self.notch60.setStatusTip("notch Filter 60 apply")
        self.notch60.setCheckable(True)
        self.notch60.triggered.connect(self.notch60Button)
        self.notch50 = QAction("50Hz", self)
        self.notch50.setStatusTip("notch Filter 50 apply")
        self.notch50.setCheckable(True)
        self.notch50.triggered.connect(self.notch50Button)
        self.notchNone = QAction("&Off", self)
        self.notchNone.setStatusTip("notch Filter not apply")
        self.notchNone.setCheckable(True)
        self.notchNone.triggered.connect(self.notchNoneButton)
        self.notchActionGroup = QActionGroup(self)
        self.notchActionGroup.addAction(self.notch60)
        self.notchActionGroup.addAction(self.notch50)
        self.notchActionGroup.addAction(self.notchNone)
        self.notch60.setChecked(True)
        self.notchActionGroup.triggered.connect(self.setNotch)

        self.lowPassNone = QAction("Off", self)
        self.lowPassNone.setStatusTip("low pass Filter not apply")
        self.lowPassNone.setCheckable(True)
        self.lowPassNone.triggered.connect(self.lowPassNoneButton)
        self.lowPass50 = QAction("S10 : 1-20 Hz", self)  # bandpass change
        self.lowPass50.setStatusTip("band pass Filter apply")
        self.lowPass50.setCheckable(True)
        self.lowPass50.triggered.connect(self.lowPass50Button)
        self.bandpass50 = QAction("S20 : 1-50Hz", self)
        self.bandpass50.setCheckable(True)
        self.bandpass50.triggered.connect(self.bandpass50Button)
        self.lowPassActionGroup = QActionGroup(self)
        self.lowPassActionGroup.addAction(self.lowPassNone)
        self.lowPassActionGroup.addAction(self.lowPass50)
        self.lowPassActionGroup.addAction(self.bandpass50)
        self.bandpass50.setChecked(True)
        self.lowPassActionGroup.triggered.connect(self.setLowPass)
        '''
        # #fft channel change
        self.FFT_Ch1 = QAction("FFT_Ch1", self)
        self.FFT_Ch1.setCheckable(True)
        self.FFT_Ch1.triggered.connect(self.FFT_Ch1Button)
        self.FFT_Ch2 = QAction("FFT_Ch2", self)
        self.FFT_Ch2.setCheckable(True)
        self.FFT_Ch2.triggered.connect(self.FFT_Ch2Button)
        self.FFT_ChangeActionGroup = QActionGroup(self)
        self.FFT_ChangeActionGroup.addAction(self.FFT_Ch1)
        self.FFT_ChangeActionGroup.addAction(self.FFT_Ch2)
        self.FFT_Ch1.setChecked(True)
        self.FFT_ChangeActionGroup.triggered.connect(self.set_FFT_Ch)
        '''
        # about
        self.aboutAction = QAction("&About", self)
        self.aboutAction.setStatusTip("Show the application's About box")
        self.aboutAction.triggered.connect(self.about)

        # development screen
        self.developmentScreen = QAction("&Development", self)
        self.developmentScreen.setStatusTip(" 개발자 창을 생성한다.")
        self.developmentScreen.triggered.connect(self.developWindow)

        # createMenus
        fileMenu = self.menuBar().addMenu("&File")
        fileMenu.addAction(self.save)
        fileMenu.addAction(self.exitAction)
        ControlMenu = self.menuBar().addMenu("&Control")
        ControlMenu.addAction(self.scan)
        ControlMenu.addAction(self.connection)
        #ControlMenu.addAction(self.disconnection)
        ControlMenu.addAction(self.stop)
        ControlMenu.addAction(self.paused)
        LEDMenu = self.menuBar().addMenu("&LED")
        LEDMenu.addAction(self.powerLED)
        LEDMenu.addAction(self.BLELED)
        NotchMenu = self.menuBar().addMenu("&Notch")
        NotchMenu.addAction(self.notchNone)
        NotchMenu.addAction(self.notch50)
        NotchMenu.addAction(self.notch60)
        LowPassMenu = self.menuBar().addMenu("&Filter")
        LowPassMenu.addAction(self.lowPassNone)
        LowPassMenu.addAction(self.lowPass50)
        LowPassMenu.addAction(self.bandpass50)
        '''
        FFTChangeMenu = self.menuBar().addMenu("&3D_FFT_Ch")
        FFTChangeMenu.addAction(self.FFT_Ch1)
        FFTChangeMenu.addAction(self.FFT_Ch2)
        '''
        helpMenu = self.menuBar().addMenu("&Help")
        helpMenu.addAction(self.aboutAction)

        # createToolBar
        pgToolBar = self.addToolBar("PG")
        pgToolBar.setObjectName("PGToolBar")
        pgToolBar.addAction(self.scan)
        pgToolBar.addAction(self.connection)
        #pgToolBar.addAction(self.disconnection)
        pgToolBar.addSeparator()
        pgToolBar.addAction(self.stop)
        pgToolBar.addAction(self.paused)
        pgToolBar.addAction(self.save)
        pgToolBar.addSeparator()
        pgToolBar.addAction(self.powerLED)
        pgToolBar.addAction(self.BLELED)
        pgToolBar.addSeparator()
        pgToolBar.addAction(self.USB_Plug)
        pgToolBar.addAction(self.HwVersionConfirm)

    def detection_callback(self, *args):
        ss = str(args)
        '''
        self.listWidget2.addItem(ss)
        self.printIndex2 += 1
        if self.printIndex2 > 7:
            self.listWidget2.takeItem(0)
        '''
    def autoScan(self):
        asyncio.ensure_future(self.scan_start(), loop=loop)
        #self.listWidget2.takeItem(0)
        #self.listWidget2.addItem("scan start")

    def connectEnable(self):
        if not self.conBool:
            self.connection.setEnabled(True)

    async def scan_start(self):
        #self.scanner.register_detection_callback(self.detection_callback)
        self.lLabel.setText("Scan 중")
        self.tableWidgetScan.clear()
        self.scanner = BleakScanner()
        self.scanner.set_scanning_filter()
        await self.scanner.start()
        await asyncio.sleep(5.0)
        await self.scanner.stop()
        devices = self.scanner.discovered_devices
        col = 0
        row = len(devices)
        self.tableWidgetScan.setRowCount(row)
        for d in devices:
            ss = str(d)
            #self.listWidget2.takeItem(0)
            #self.listWidget2.addItem(ss)
            name = str(d.name)
            item_name = QTableWidgetItem(name)
            item_address = QTableWidgetItem(d.address)
            rss = str(d.rssi)
            item_rssi = QTableWidgetItem(rss)
            self.tableWidgetScan.setItem(col, 0, item_name)
            self.tableWidgetScan.setItem(col, 1, item_address)
            self.tableWidgetScan.setItem(col, 2, item_rssi)
            col += 1
        if not devices:
            self.lLabel.setText("bluetooth 동글 꽂는걸 깜빡하셨나 보네요")
        self.lLabel.setText("Scan 끝. 원하는 기기를 못찾으면 Scan버튼 한번 더 누르시오.")

    async def connect_panax(self, address, loop):
        self.client = BleakClient(address, loop=loop)
        while not self.noexcept:
            try:
                await self.client.connect()
                await self.isConnected()
                self.paused.setEnabled(True)
                self.BLELED.setEnabled(True)
                self.powerLED.setEnabled(True)
                self.USB_Plug.setEnabled(True)
                self.HwVersionConfirm.setEnabled(True)
                self.noexcept = True
                #self.listWidget2.takeItem(0)
                #self.listWidget2.addItem("Connect complete")
                self.lLabel.setText("연결이 완료 되었습니다. 측정시작 버튼을 눌러주세요")
                self.connection.setDisabled(True)
                self.disconnection.setEnabled(True)
                await self.client.start_notify(self.USB_Plug_UUID, self.USB_Plug_received)
            except Exception as e:
                #self.listWidget2.takeItem(0)
                #self.listWidget2.addItem(str(e))
                self.lLabel.setText("Connection 중")

    async def isConnected(self):
        self.conBool = self.client.is_connected
        #self.listWidget2.takeItem(0)
        #self.listWidget2.addItem(str(self.conBool))

    async def disconnect(self):
        await self.client.disconnect()
        await self.isConnected()
        #self.listWidget2.takeItem(0)
        #self.listWidget2.addItem("disconnected success")

    async def disconnect_panax(self):
        await self.client.stop_notify(self.Read_UUID)

    async def write_panax(self):
        await self.client.write_gatt_char(self.Write_UUID, data=self.byteWrite)
        #self.listWidget2.takeItem(0)
        #self.listWidget2.addItem("BLE 01 write")

    async def start_panax(self):
        if self.conBool:
            await self.client.start_notify(self.Read_UUID, self.tx_data_received)
            self.paused.setEnabled(True)

    async def PowerLEDOn(self):
        if self.conBool:
            self.byteLED = 1
            writeByte = bytearray([self.byteLED])
            print(writeByte)
            await self.client.write_gatt_char(self.Power_UUID, data=writeByte)

    async def PowerLEDOff(self):
        if self.conBool:
            self.byteLED = 0
            writeByte = bytearray([self.byteLED])
            print(writeByte)
            await self.client.write_gatt_char(self.Power_UUID, data=writeByte)

    async def BLELEDOn(self):
        if self.conBool:
            self.byteLED = 2
            writeByte = bytearray([self.byteLED])
            print(writeByte)
            await self.client.write_gatt_char(self.BLE_UUID, data=writeByte)

    async def BLELEDOff(self):
        if self.conBool:
            self.byteLED = 0
            writeByte = bytearray([self.byteLED])
            print(writeByte)
            await self.client.write_gatt_char(self.BLE_UUID, data=writeByte)

    async def USB_PlugConfirmOn(self):
        await self.client.start_notify(self.USB_Plug_UUID, self.USB_Plug_received)

    async def aHwVersionConfirm(self):
        self.HwVersion = await self.client.read_gatt_char(self.HwVersion_UUID)
        str_hw = str(self.HwVersion)
        self.lLabel.setText(str_hw)

    def powerLEDOnOff(self):
        self.boolPower = not self.boolPower
        if self.boolPower:
            asyncio.ensure_future(self.PowerLEDOn())
            self.powerLED.setIcon(QIcon("./images/pwrLEDGray.png"))
        else:
            asyncio.ensure_future(self.PowerLEDOff())
            self.powerLED.setIcon(QIcon("./images/pwrLED.png"))

    def BLELEDOnOff(self):
        self.boolBLELED = not self.boolBLELED
        if self.boolBLELED:
            asyncio.ensure_future(self.BLELEDOn())
            self.BLELED.setIcon(QIcon("./images/BLEGray.png"))
        else:
            asyncio.ensure_future(self.BLELEDOff())
            self.BLELED.setIcon(QIcon("./images/BLE.png"))

    def USB_PlugConfirmButton(self):
        asyncio.ensure_future(self.USB_PlugConfirmOn())

    def HwVersionConfirmButton(self):
        asyncio.ensure_future(self.aHwVersionConfirm())

    def notch60Button(self):
        self.notchSelect = notchFilterSelect.notch60

    def notch50Button(self):
        self.notchSelect = notchFilterSelect.notch50

    def notchNoneButton(self):
        self.notchSelect = notchFilterSelect.none

    def setNotch(self, action):
        if action == self.notch60:
            self.notch60Button()
        elif action == self.notch50:
            self.notch50Button()
        else:
            self.notchNoneButton()

    def setLowPass(self, action):
        if action == self.lowPassNone:
            self.lowPassNoneButton()
        elif action == self.lowPass50:
            self.lowPass50Button()
        else:
            self.bandpass50Button()

    def lowPassNoneButton(self):
        self.lowPassSelect = lowPassFilterSelect.none
        self.ax1.enableAutoRange(axis='y', enable=True)
        self.ax3.enableAutoRange(axis='y', enable=True)

    def lowPass50Button(self):
        self.lowPassSelect = lowPassFilterSelect.lpf50
        self.ax1.setRange(xRange=[-5, 0], yRange=[-100, 100])
        self.ax3.setRange(xRange=[-5, 0], yRange=[-100, 100])

    def bandpass50Button(self):
        self.lowPassSelect = lowPassFilterSelect.bpf2_50
        self.ax1.setRange(xRange=[-5, 0], yRange=[-100, 100])
        self.ax3.setRange(xRange=[-5, 0], yRange=[-100, 100])

    def set_FFT_Ch(self, action):
        if action == self.FFT_Ch1:
            self.FFT_Ch1Button()
        else:
            self.FFT_Ch2Button()

    def FFT_Ch1Button(self):
        self.FFT_Select = FFT_Channel_Select.ch1
        for band in eeg_bands:
            self.freq_ix[band] = np.where((self.frequencies >= eeg_bands[band][0])
                                          & (self.frequencies <= eeg_bands[band][1]))[0]
            self.freqBand[band] = self.frequencies[self.freq_ix[band]]
            self.ampBand[band] = np.zeros((len(self.freq_ix[band]), 120))
            self.Time[band] = np.linspace(0, 119, 120)
            self.Fre[band] = self.freqBand[band]
            self.cMap = plt.get_cmap(cMapList[band])
            self.CvMax[band] = self.cMap(self.ampBand[band] / self.fftHeight)

    def FFT_Ch2Button(self):
        self.FFT_Select = FFT_Channel_Select.ch2
        for band in eeg_bands:
            self.freq_ix[band] = np.where((self.frequencies >= eeg_bands[band][0])
                                          & (self.frequencies <= eeg_bands[band][1]))[0]
            self.freqBand[band] = self.frequencies[self.freq_ix[band]]
            self.ampBand[band] = np.zeros((len(self.freq_ix[band]), 120))
            self.Time[band] = np.linspace(0, 119, 120)
            self.Fre[band] = self.freqBand[band]
            self.cMap = plt.get_cmap(cMapList[band])
            self.CvMax[band] = self.cMap(self.ampBand[band] / self.fftHeight)

    def connectAddress(self):
        if not self.boolConnectAttempt:
            self.boolConnectAttempt = True
            items = self.tableWidgetScan.selectedItems()
            self.macAddress = items[1].text()
            self.lLabel.setText("connection을 진행합니다.")
            #self.listWidget2.takeItem(0)
            #self.listWidget2.addItem(self.macAddress)
            asyncio.ensure_future(self.connect_panax(self.macAddress, loop), loop=loop)

    def disconnectAddress(self):
        self.noexcept = False
        asyncio.ensure_future(self.disconnect())
        self.tableWidgetScan.clearContents()
        self.paused.setDisabled(True)
        self.BLELED.setDisabled(True)
        self.powerLED.setDisabled(True)
        self.USB_Plug.setDisabled(True)
        self.HwVersionConfirm.setDisabled(True)
        self.connection.setDisabled(True)
        self.boolConnectAttempt = False
        self.lLabel.setText("Disconnection 하였습니다.")

    def measureStart(self):
        asyncio.ensure_future(self.isConnected())
        asyncio.ensure_future(self.write_panax())
        asyncio.ensure_future(self.start_panax(), loop=loop)
        self.save.setEnabled(True)
        self.USB_Plug.setDisabled(True)
        self.HwVersionConfirm.setDisabled(True)
        self.powerLED.setDisabled(True)
        self.BLELED.setDisabled(True)
        self.lLabel.setText("뇌파를 측정중입니다.")

    # event
    def save_xml(self):
        xml_write.indent(self.user)
        now = datetime.datetime.now()
        nowDate = now.strftime('%Y-%m-%d.%H.%M')
        nowXml = nowDate + '.xml'
        ET.ElementTree(self.user).write(nowXml)
        nowXml = "저장이 완료 되었습니다" + nowXml
        self.lLabel.setText(nowXml)

    def stopDialog(self):
        sd = stopdialog.Ui_dialog(self)
        if sd.exec():
            self.plotInit()

    def startMeasureBtn(self):
        if not self.boolFirstStart:
            self.paused.setIcon(QIcon("./images/pauseBlue2.png"))
            self.boolFirstStart = True
            self.measureStart()
        else:
            self.pausedMeasure()

    def pausedMeasure(self):
        self.boolPaused = not self.boolPaused
        if not self.boolPaused:
            asyncio.ensure_future(self.disconnect_panax())
            self.paused.setIcon(QIcon("./images/playBlue.png"))
            self.stop.setEnabled(True)
            self.lLabel.setText("측정을 정지합니다.")
        else:
            self.measureStart()
            self.paused.setIcon(QIcon("./images/pauseBlue.png"))
            self.stop.setDisabled(True)
            self.lLabel.setText("측정을 재개합니다.")

    def plotInit(self):
        self.paused.setIcon(QIcon("./images/playBlue2.png"))
        self.paused.setEnabled(True)
        self.lLabel.setText("측정을 초기화 하였습니다.")
        if self.boolPaused:
            self.pausedMeasure()
        # asyncio.ensure_future(self.disconnect())
        self.timerCounter = 0
        self.printIndex = 0
        self.printIndex2 = 0
        self.ch1_1_value = 0
        self.ch1_2_value = 0
        self.ch1_3_value = 0
        self.ch2_1_value = 0
        self.ch2_2_value = 0
        self.ch2_3_value = 0
        self.dataIndex = 0
        self.boolFirstStart = False
        self.boolPaused = True
        self.pwrBtnStr = "Pwr :"
        self.boolPower = False
        self.boolBLELED = False
        self.boolConnectAttempt = False
        self.fData.clear()
        self.fData2.clear()
        self.fData3.clear()
        self.fData4.clear()
        self.fData = deque(np.zeros(self.dequeMax), maxlen=self.dequeMax)
        self.fData2 = deque(np.zeros(self.dequeMax), maxlen=self.dequeMax)
        self.fData3 = deque(np.zeros(self.fftMax), maxlen=self.fftMax)
        self.fData4 = deque(np.zeros(self.fftMax), maxlen=self.fftMax)
        self.line1.setData(np.empty(1))
        self.line2.setData(np.empty(1))
        #self.line3.setData(np.empty(1))
        #self.line4.setData(np.empty(1))
        #self.line_fft.setData(np.empty(1))
        #self.line_fft_ch2.setData(np.empty(1))
        self.data1 = np.zeros(30000)
        self.data2 = np.zeros(30000)
        self.data3 = np.zeros(30000)
        self.data1_x = np.linspace(0, 29999, 30000) * 0.004
        self.data2_x = np.linspace(0, 29999, 30000) * 0.004
        self.data3_x = np.linspace(0, 29999, 30000) * 0.004
        self.data4 = np.zeros(30000)
        self.data4_x = np.linspace(0, 29999, 30000) * 0.004
        #self.data_fft = np.zeros(50)
        #self.data_fft_x = np.linspace(0, 49, 50)
        #self.data_fft_ch2 = np.zeros(50)
        #self.data_fft_ch2_x = np.linspace(0, 49, 50)
        '''
        for band in eeg_bands:
            self.freq_ix[band] = np.where((self.frequencies >= eeg_bands[band][0])
                                          & (self.frequencies <= eeg_bands[band][1]))[0]
            self.freqBand[band] = self.frequencies[self.freq_ix[band]]
            self.ampBand[band] = np.zeros((len(self.freq_ix[band]), 120))
            self.Time[band] = np.linspace(0, 119, 120)
            self.Fre[band] = self.freqBand[band]
            self.cMap = plt.get_cmap(cMapList[band])
            self.CvMax[band] = self.cMap(self.ampBand[band] / self.fftHeight)
        '''
        self.disconnectAddress()
        self.stop.setDisabled(True)
        self.powerLED.setDisabled(True)
        self.BLELED.setDisabled(True)
        self.USB_Plug.setDisabled(True)
        self.HwVersionConfirm.setDisabled(True)
        # self.tableWidgetScan.clearContents()
        asyncio.ensure_future(self.isConnected())

    def about(self):
        QMessageBox.about(self, "About Shape",
                          "<h2>Brint Monitor 1.0</h2>"
                          "<p>Copyright &copy; 2020 Panaxtos Inc."
                          "<p>Shape is a small application that "
                          "demonstrates QAction, QMainWindow, QMenuBar, "
                          "QStatusBar, QToolBar, and many other "
                          )

    def developWindow(self):
        print("develop")

    # data_received -> parsing -> int -> 20 -> print
    def rx_data_received(self, sender, data):
        print("RX {}".format(data))

    def USB_Plug_received(self, sender, data):
        self.USB_Plug_Count += 1
        sec = self.USB_Plug_Count
        minute = int(sec / 60)
        hour = int(minute / 60)
        sec = int(sec % 60)
        minute = int(minute % 60)
        int_Data = data[0]
        self.battery_array.append(int_Data)
        cnt = Counter(self.battery_array)
        mode = cnt.most_common(1)
        int_Data = mode[0][0]
        if int_Data > 128:
            str_MSB = "1"
            bat = int_Data - 128
        else:
            str_MSB = "0"
            bat = int_Data
        str_usb = str(hour) + "h " + str(minute) + "m " + str(sec) + "s " + ": MSB="
        str_usb += str_MSB + " , BAT="
        if bat > 74:
            str_bat = "100%"
        elif bat > 68:
            str_bat = remaining_battery(bat)
        else:
            str_bat = str(bat)
        str_usb += str_bat
        self.lLabel_battery.setText(str_usb)

    def tx_data_received(self, sender, data):
        str_data = data[0]
        str_data = repr(str_data)
        self.listWidget.addItem(str_data)
        self.printIndex += 1
        if self.printIndex > 38:
            self.listWidget.takeItem(0)
        data_len = len(data)
        for rep in range(data_len):
            if rep < 31:
                if rep != 0:
                    self.bufferLeft.append(data[rep])
            else:
                if rep != 31:
                    self.bufferRight.append(data[rep])
        self.read_data()
        if len(self.ch1_int_buffer) >= self.update_num and len(self.ch2_int_buffer) >= self.update_num:
            self.print_graph()
            self.timerCounter += 1
        '''
        if self.timerCounter >= self.rawGraphFrame:
            self.timerCounter -= self.rawGraphFrame
            self.printFFTGraph()
        '''
    def read_data(self):
        while len(self.bufferLeft) > 0:
            ch1_1_value = self.bufferLeft.pop(0)
            ch1_2_value = self.bufferLeft.pop(0)
            ch1_3_value = self.bufferLeft.pop(0)
            ch2_1_value = self.bufferRight.pop(0)
            ch2_2_value = self.bufferRight.pop(0)
            ch2_3_value = self.bufferRight.pop(0)

            ch1_int = (ch1_1_value * self.two_16) + (ch1_2_value * self.two_8) + ch1_3_value
            ch1_int = tc.twos_comp(ch1_int, 24)
            ch1_int = ch1_int * self.max_uv / 1000 * 1.31
            self.ch1_int_buffer.append(ch1_int)
            ch2_int = (ch2_1_value * self.two_16) + (ch2_2_value * self.two_8) + ch2_3_value
            ch2_int = tc.twos_comp(ch2_int, 24)
            ch2_int = ch2_int * self.max_uv / 1000 * 1.31
            self.ch2_int_buffer.append(ch2_int)
            # self.dataIndex += 1
            # data = xml_write.makeXML(self.dataIndex, ch1_int, ch2_int)
            # self.user.append(data)

    def print_graph(self):
        ch1 = []
        ch2 = []
        for rep in range(0, self.update_num):
            temp = self.ch1_int_buffer.pop(0)
            temp2 = self.ch2_int_buffer.pop(0)
            ch1.append(temp)
            ch2.append(temp2)
        self.fData.extend(ch1)
        self.fData2.extend(ch2)
        filtering_ch1 = list(self.fData)
        filtering_ch2 = list(self.fData2)
        filtering_ch1_alpha = list(self.fData)
        filtering_ch2_alpha = list(self.fData2)
        if self.notchSelect == notchFilterSelect.none:
            pass
        elif self.notchSelect == notchFilterSelect.notch60:
            self.notchCutOff = 60
            notch_ch1 = nf.notch_filter(filtering_ch1, self.notchCutOff, self.samplingRate, self.notchQualityFactor)
            notch_ch2 = nf.notch_filter(filtering_ch2, self.notchCutOff, self.samplingRate, self.notchQualityFactor)
            filtering_ch1 = nf.notch_filter(notch_ch1, self.notchCutOff, self.samplingRate, self.notchQualityFactor)
            filtering_ch2 = nf.notch_filter(notch_ch2, self.notchCutOff, self.samplingRate, self.notchQualityFactor)
        else:
            self.notchCutOff = 50
            notch_ch1 = nf.notch_filter(filtering_ch1, self.notchCutOff, self.samplingRate, self.notchQualityFactor)
            notch_ch2 = nf.notch_filter(filtering_ch2, self.notchCutOff, self.samplingRate, self.notchQualityFactor)
            filtering_ch1 = nf.notch_filter(notch_ch1, self.notchCutOff, self.samplingRate, self.notchQualityFactor)
            filtering_ch2 = nf.notch_filter(notch_ch2, self.notchCutOff, self.samplingRate, self.notchQualityFactor)
        filtering_ch1_alpha = filtering_ch1
        filtering_ch2_alpha = filtering_ch2
        if self.lowPassSelect == lowPassFilterSelect.none:
            pass
        elif self.lowPassSelect == lowPassFilterSelect.lpf50:
            filtering_ch1 = bf.butter_bandpass_filter(filtering_ch1, 1, 20, self.samplingRate, 7)
            filtering_ch2 = bf.butter_bandpass_filter(filtering_ch2, 1, 20, self.samplingRate, 7)
        else:
            filtering_ch1 = bf.butter_bandpass_filter(filtering_ch1, 1, 50, self.samplingRate, 7)
            filtering_ch2 = bf.butter_bandpass_filter(filtering_ch2, 1, 50, self.samplingRate, 7)

        filtering_ch1_alpha = bf.butter_bandpass_filter(filtering_ch1, 8, 13, self.samplingRate, 5)
        filtering_ch2_alpha = bf.butter_bandpass_filter(filtering_ch2, 8, 13, self.samplingRate, 5)
        self.fData3.extend(filtering_ch1[-self.update_num:])
        self.fData4.extend(filtering_ch2[-self.update_num:])

        self.data3[:-self.update_num] = self.data3[self.update_num:]
        self.data3[-self.update_num:] = filtering_ch1[-self.update_num:]
        self.data4[:-self.update_num] = self.data4[self.update_num:]
        self.data4[-self.update_num:] = filtering_ch2[-self.update_num:]
        self.data1[:-self.update_num] = self.data1[self.update_num:]
        self.data1[-self.update_num:] = filtering_ch1_alpha[-self.update_num:]
        self.data2[:-self.update_num] = self.data2[self.update_num:]
        self.data2[-self.update_num:] = filtering_ch2_alpha[-self.update_num:]
        self.line1.setData(x=self.data3_x, y=self.data3)
        self.line1.setPos(-120, 0)
        self.line2.setData(x=self.data4_x, y=self.data4)
        self.line2.setPos(-120, 0)
        #self.line3.setData(x=self.data1_x, y=self.data1)
        #self.line3.setPos(-120, 0)
        #self.line4.setData(x=self.data2_x, y=self.data2)
        #self.line4.setPos(-120, 0)

    def printFFTGraph(self):
        ch1_raw_data = self.fData3
        ch2_raw_data = self.fData4
        self.fftIndex += 1
        ch1_fft = np.fft.fft(ch1_raw_data) / len(ch1_raw_data)
        ch1_fft = 2.0 * np.absolute(ch1_fft)
        ch1_fft = np.delete(ch1_fft, 0, axis=0)
        ch1_fft = ch1_fft[:60]

        ch2_fft = np.fft.fft(ch2_raw_data) / len(ch2_raw_data)
        ch2_fft = 2.0 * np.absolute(ch2_fft)
        ch2_fft = np.delete(ch2_fft, 0, axis=0)
        ch2_fft = ch2_fft[:60]

        for band in eeg_bands:
            tmp = self.ampBand[band][:, 1:]
            if self.FFT_Select == FFT_Channel_Select.ch1:
                self.ampBand[band][:, -1] = ch1_fft[self.freq_ix[band][0]: self.freq_ix[band][-1] + 1]
            else:
                self.ampBand[band][:, -1] = ch2_fft[self.freq_ix[band][0]: self.freq_ix[band][-1] + 1]
            self.ampBand[band][:, :-1] = tmp
            self.cMap = plt.get_cmap('jet')
            self.CvMax[band] = self.cMap(self.ampBand[band] / self.fftHeight)
            self.surfPlot[band].setData(z=self.ampBand[band], colors=self.CvMax[band])
        # fft_node = fft_xml_write.makeXML(self.fftIndex, ch1_fft)
        # self.user.append(fft_node)
        self.line_fft.setData(x=self.frequencies, y=ch1_fft)
        self.line_fft_ch2.setData(x=self.frequencies, y=ch2_fft)


eeg_bands = {'Delta': (1, 3),
             'Theta': (4, 7),
             'Alpha': (8, 12),
             'Beta': (13, 30),
             'Gamma': (31, 50)
             }

cMapList = {'Delta': plt.cm.Reds,
            'Theta': plt.cm.Oranges,
            'Alpha': plt.cm.Wistia,
            'Beta': plt.cm.BuGn,
            'Gamma': plt.cm.YlGnBu
            }


def remaining_battery(x):
    return {78: "100%",
            77: "99%",
            76: "99%",
            75: "100%",
            74: "95%",
            73: "90%",
            72: "80%",
            71: "60%",
            70: "40%",
            69: "20%"
            # 68: "15%",
            # 67: "10%",
            # 64: "5%",
            # 62: "4%",
            # 58: "3%",
            # 51: "0%"
            }[x]


COMPLETED_STYLE = """
QProgressBar::chunk {
       background-color: #FFBE0E;
       border: 2px solid grey;
       border-radius: 5px;
       text-align: center;
       margin: 1px;
}
"""


class notchFilterSelect(enum.Enum):
    notch60 = 0
    notch50 = 1
    none = 2


class lowPassFilterSelect(enum.Enum):
    none = 0
    lpf50 = 1
    bpf2_50 = 2
    lpf21 = 3
    lpf13 = 4


class FFT_Channel_Select(enum.Enum):
    ch1 = 0
    ch2 = 1


if __name__ == '__main__':
    app = QApplication(sys.argv)
    if app is None:
        app = QApplication([])
    loop = quamash.QEventLoop(app)
    asyncio.set_event_loop(loop)
    splash_pix = QPixmap('./images/splash.png')
    splash = QSplashScreen(splash_pix, Qt.WindowStaysOnTopHint)
    splash.setWindowFlags(Qt.WindowStaysOnTopHint | Qt.FramelessWindowHint)
    splash.setEnabled(False)
    # adding progress bar
    progressBar = QProgressBar(splash)
    progressBar.setMaximum(10)
    progressBar.setGeometry(70, splash_pix.height() - 120, splash_pix.width() - 140, 20)
    progressBar.setStyleSheet(COMPLETED_STYLE)
    progressBar.setAlignment(Qt.AlignCenter)
    splash.show()

    for i in range(1, 11):
        progressBar.setValue(i)
        t = time()
        while time() < t + 0.1:
            app.processEvents()
    with loop:
        window33 = MainWindow()
        window33.show()
        splash.finish(window33)
        # sys.exit(app.exec_())
        loop.run_forever()