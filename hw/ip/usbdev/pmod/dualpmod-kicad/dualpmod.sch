EESchema Schematic File Version 4
EELAYER 30 0
EELAYER END
$Descr A4 11693 8268
encoding utf-8
Sheet 1 1
Title ""
Date ""
Rev ""
Comp ""
Comment1 ""
Comment2 ""
Comment3 ""
Comment4 ""
$EndDescr
$Comp
L dualpmod-rescue:68021-412HLF-dk_Rectangular-Connectors-Headers-Male-Pins J3
U 1 1 5C7E600E
P 5550 2000
F 0 "J3" H 5550 2447 60  0000 C CNN
F 1 "68021-412HLF" H 5550 2341 60  0000 C CNN
F 2 "digikey-footprints:PinHeader_6x2_P2.54mm_Horizontal" H 5750 2200 60  0001 L CNN
F 3 "https://cdn.amphenol-icc.com/media/wysiwyg/files/drawing/68020.pdf" H 5750 2300 60  0001 L CNN
F 4 "609-3355-ND" H 5750 2400 60  0001 L CNN "Digi-Key_PN"
F 5 "68021-412HLF" H 5750 2500 60  0001 L CNN "MPN"
F 6 "Connectors, Interconnects" H 5750 2600 60  0001 L CNN "Category"
F 7 "Rectangular Connectors - Headers, Male Pins" H 5750 2700 60  0001 L CNN "Family"
F 8 "https://cdn.amphenol-icc.com/media/wysiwyg/files/drawing/68020.pdf" H 5750 2800 60  0001 L CNN "DK_Datasheet_Link"
F 9 "/product-detail/en/amphenol-icc-fci/68021-412HLF/609-3355-ND/1878558" H 5750 2900 60  0001 L CNN "DK_Detail_Page"
F 10 "CONN HEADER R/A 12POS 2.54MM" H 5750 3000 60  0001 L CNN "Description"
F 11 "Amphenol ICC (FCI)" H 5750 3100 60  0001 L CNN "Manufacturer"
F 12 "Active" H 5750 3200 60  0001 L CNN "Status"
	1    5550 2000
	1    0    0    -1  
$EndComp
$Comp
L Device:R_Small_US R4
U 1 1 5C7E65B5
P 3900 2300
F 0 "R4" V 3695 2300 50  0000 C CNN
F 1 "22R" V 3786 2300 50  0000 C CNN
F 2 "Resistor_SMD:R_0805_2012Metric_Pad1.15x1.40mm_HandSolder" H 3900 2300 50  0001 C CNN
F 3 "~" H 3900 2300 50  0001 C CNN
	1    3900 2300
	0    1    1    0   
$EndComp
$Comp
L Device:R_Small_US R3
U 1 1 5C7E6727
P 3900 1900
F 0 "R3" V 3695 1900 50  0000 C CNN
F 1 "22R" V 3786 1900 50  0000 C CNN
F 2 "Resistor_SMD:R_0805_2012Metric_Pad1.15x1.40mm_HandSolder" H 3900 1900 50  0001 C CNN
F 3 "~" H 3900 1900 50  0001 C CNN
	1    3900 1900
	0    1    1    0   
$EndComp
Wire Wire Line
	3800 1900 3450 1900
$Comp
L Device:R_Small_US R9
U 1 1 5C7E74B9
P 4750 2100
F 0 "R9" V 4545 2100 50  0000 C CNN
F 1 "1k5" V 4636 2100 50  0000 C CNN
F 2 "Resistor_SMD:R_0805_2012Metric_Pad1.15x1.40mm_HandSolder" H 4750 2100 50  0001 C CNN
F 3 "~" H 4750 2100 50  0001 C CNN
	1    4750 2100
	0    1    1    0   
$EndComp
Wire Wire Line
	5350 2100 4850 2100
Wire Wire Line
	5350 1800 5100 1800
Wire Wire Line
	5100 1800 5100 1400
Wire Wire Line
	5100 1400 5500 1400
Wire Wire Line
	6000 1400 6000 1800
Wire Wire Line
	6000 1800 5750 1800
$Comp
L Device:R_Small_US R5
U 1 1 5C7E7B21
P 3950 2950
F 0 "R5" V 3745 2950 50  0000 C CNN
F 1 "22R" V 3836 2950 50  0000 C CNN
F 2 "Resistor_SMD:R_0805_2012Metric_Pad1.15x1.40mm_HandSolder" H 3950 2950 50  0001 C CNN
F 3 "~" H 3950 2950 50  0001 C CNN
	1    3950 2950
	0    1    1    0   
$EndComp
$Comp
L Device:R_Small_US R6
U 1 1 5C7E7B28
P 3950 3700
F 0 "R6" V 3745 3700 50  0000 C CNN
F 1 "22R" V 3836 3700 50  0000 C CNN
F 2 "Resistor_SMD:R_0805_2012Metric_Pad1.15x1.40mm_HandSolder" H 3950 3700 50  0001 C CNN
F 3 "~" H 3950 3700 50  0001 C CNN
	1    3950 3700
	0    1    1    0   
$EndComp
Wire Wire Line
	6100 2950 6100 2300
Wire Wire Line
	6100 2300 5750 2300
Wire Wire Line
	4050 3700 6150 3700
Wire Wire Line
	6150 3700 6150 2200
Wire Wire Line
	6150 2200 5750 2200
$Comp
L Device:R_Small_US R10
U 1 1 5C7E88E5
P 6500 2700
F 0 "R10" H 6568 2746 50  0000 L CNN
F 1 "1k5" H 6568 2655 50  0000 L CNN
F 2 "Resistor_SMD:R_0805_2012Metric_Pad1.15x1.40mm_HandSolder" H 6500 2700 50  0001 C CNN
F 3 "~" H 6500 2700 50  0001 C CNN
	1    6500 2700
	1    0    0    -1  
$EndComp
$Comp
L power:GND #PWR0101
U 1 1 5C7EB723
P 1800 2650
F 0 "#PWR0101" H 1800 2400 50  0001 C CNN
F 1 "GND" H 1805 2477 50  0000 C CNN
F 2 "" H 1800 2650 50  0001 C CNN
F 3 "" H 1800 2650 50  0001 C CNN
	1    1800 2650
	1    0    0    -1  
$EndComp
$Comp
L power:GND #PWR0102
U 1 1 5C7EB75D
P 6050 1000
F 0 "#PWR0102" H 6050 750 50  0001 C CNN
F 1 "GND" H 6055 827 50  0000 C CNN
F 2 "" H 6050 1000 50  0001 C CNN
F 3 "" H 6050 1000 50  0001 C CNN
	1    6050 1000
	1    0    0    -1  
$EndComp
Wire Wire Line
	5750 1900 6300 1900
$Comp
L power:GND #PWR0103
U 1 1 5C7ED732
P 4050 1500
F 0 "#PWR0103" H 4050 1250 50  0001 C CNN
F 1 "GND" H 4055 1327 50  0000 C CNN
F 2 "" H 4050 1500 50  0001 C CNN
F 3 "" H 4050 1500 50  0001 C CNN
	1    4050 1500
	1    0    0    -1  
$EndComp
$Comp
L Device:R_Small_US R7
U 1 1 5C7F09F9
P 4050 900
F 0 "R7" H 4118 946 50  0000 L CNN
F 1 "5k1" H 4118 855 50  0000 L CNN
F 2 "Resistor_SMD:R_0805_2012Metric_Pad1.15x1.40mm_HandSolder" H 4050 900 50  0001 C CNN
F 3 "~" H 4050 900 50  0001 C CNN
	1    4050 900 
	1    0    0    -1  
$EndComp
$Comp
L Device:R_Small_US R8
U 1 1 5C7F0A6A
P 4050 1300
F 0 "R8" H 4118 1346 50  0000 L CNN
F 1 "5k1" H 4118 1255 50  0000 L CNN
F 2 "Resistor_SMD:R_0805_2012Metric_Pad1.15x1.40mm_HandSolder" H 4050 1300 50  0001 C CNN
F 3 "~" H 4050 1300 50  0001 C CNN
	1    4050 1300
	1    0    0    -1  
$EndComp
Wire Wire Line
	4050 1000 4050 1100
Wire Wire Line
	5000 1100 4050 1100
Wire Wire Line
	4050 1100 4050 1200
Wire Wire Line
	2650 700  4050 700 
Wire Wire Line
	4050 700  4050 800 
Wire Wire Line
	5000 2000 5350 2000
Wire Wire Line
	5000 1100 5000 2000
Wire Wire Line
	5350 1900 5050 1900
Wire Wire Line
	5050 1900 5050 1000
Wire Wire Line
	5050 1000 6050 1000
Wire Wire Line
	6300 1000 6300 1900
$Comp
L power:+3.3V #PWR0104
U 1 1 5C82A21B
P 5500 1300
F 0 "#PWR0104" H 5500 1150 50  0001 C CNN
F 1 "+3.3V" H 5515 1473 50  0000 C CNN
F 2 "" H 5500 1300 50  0001 C CNN
F 3 "" H 5500 1300 50  0001 C CNN
	1    5500 1300
	1    0    0    -1  
$EndComp
Wire Wire Line
	5500 1300 5500 1400
Connection ~ 5500 1400
Wire Wire Line
	5500 1400 6000 1400
Connection ~ 4050 1100
Wire Wire Line
	4050 1400 4050 1500
$Comp
L power:GND #PWR0105
U 1 1 5C84B0AA
P 3050 4900
F 0 "#PWR0105" H 3050 4650 50  0001 C CNN
F 1 "GND" H 3055 4727 50  0000 C CNN
F 2 "" H 3050 4900 50  0001 C CNN
F 3 "" H 3050 4900 50  0001 C CNN
	1    3050 4900
	1    0    0    -1  
$EndComp
$Comp
L Device:R_Small_US R1
U 1 1 5C84B0B0
P 3050 4300
F 0 "R1" H 3118 4346 50  0000 L CNN
F 1 "5k1" H 3118 4255 50  0000 L CNN
F 2 "Resistor_SMD:R_0805_2012Metric_Pad1.15x1.40mm_HandSolder" H 3050 4300 50  0001 C CNN
F 3 "~" H 3050 4300 50  0001 C CNN
	1    3050 4300
	1    0    0    -1  
$EndComp
$Comp
L Device:R_Small_US R2
U 1 1 5C84B0B7
P 3050 4700
F 0 "R2" H 3118 4746 50  0000 L CNN
F 1 "5k1" H 3118 4655 50  0000 L CNN
F 2 "Resistor_SMD:R_0805_2012Metric_Pad1.15x1.40mm_HandSolder" H 3050 4700 50  0001 C CNN
F 3 "~" H 3050 4700 50  0001 C CNN
	1    3050 4700
	1    0    0    -1  
$EndComp
Wire Wire Line
	3050 4800 3050 4900
Connection ~ 6050 1000
Wire Wire Line
	6050 1000 6300 1000
Wire Wire Line
	5750 2000 6900 2000
Text Label 4500 1100 0    50   ~ 0
SENSE1
Text Label 6400 2000 0    50   ~ 0
SENSE2
Text Label 3150 700  0    50   ~ 0
VBUS
Text Label 3150 2300 0    50   ~ 0
DP1
Text Label 3550 1900 0    50   ~ 0
DN1
Text Label 4100 2300 0    50   ~ 0
DP1_R
Text Label 4100 1900 0    50   ~ 0
DN1_R
Text Label 4950 2100 0    50   ~ 0
PULLUP1
Text Label 5800 2100 0    50   ~ 0
PULLUP2
Text Label 4650 3700 0    50   ~ 0
DN2_R
Text Label 4650 2950 0    50   ~ 0
DP2_R
Wire Wire Line
	6900 2000 6900 4500
$Comp
L dualpmod-rescue:10118193-0001LF-dk_USB-DVI-HDMI-Connectors J2
U 1 1 5C8252B6
P 1250 1800
F 0 "J2" H 1313 2545 60  0000 C CNN
F 1 "10118193-0001LF" H 1313 2439 60  0000 C CNN
F 2 "digikey-footprints:USB_Micro_B_Female_10118193-0001LF" H 1450 2000 60  0001 L CNN
F 3 "http://www.amphenol-icc.com/media/wysiwyg/files/drawing/10118193.pdf" H 1450 2100 60  0001 L CNN
F 4 "609-4616-1-ND" H 1450 2200 60  0001 L CNN "Digi-Key_PN"
F 5 "10118193-0001LF" H 1450 2300 60  0001 L CNN "MPN"
F 6 "Connectors, Interconnects" H 1450 2400 60  0001 L CNN "Category"
F 7 "USB, DVI, HDMI Connectors" H 1450 2500 60  0001 L CNN "Family"
F 8 "http://www.amphenol-icc.com/media/wysiwyg/files/drawing/10118193.pdf" H 1450 2600 60  0001 L CNN "DK_Datasheet_Link"
F 9 "/product-detail/en/amphenol-icc-fci/10118193-0001LF/609-4616-1-ND/2785380" H 1450 2700 60  0001 L CNN "DK_Detail_Page"
F 10 "CONN RCPT USB2.0 MICRO B SMD R/A" H 1450 2800 60  0001 L CNN "Description"
F 11 "Amphenol ICC (FCI)" H 1450 2900 60  0001 L CNN "Manufacturer"
F 12 "Active" H 1450 3000 60  0001 L CNN "Status"
	1    1250 1800
	1    0    0    -1  
$EndComp
Wire Wire Line
	2650 700  2650 1600
Wire Wire Line
	2650 1600 1550 1600
Wire Wire Line
	1550 1700 3450 1700
Wire Wire Line
	1550 2000 1800 2000
NoConn ~ 1550 1900
$Comp
L dualpmod-rescue:10118193-0001LF-dk_USB-DVI-HDMI-Connectors J1
U 1 1 5C830207
P 1200 3800
F 0 "J1" H 1263 4545 60  0000 C CNN
F 1 "10118193-0001LF" H 1263 4439 60  0000 C CNN
F 2 "digikey-footprints:USB_Micro_B_Female_10118193-0001LF" H 1400 4000 60  0001 L CNN
F 3 "http://www.amphenol-icc.com/media/wysiwyg/files/drawing/10118193.pdf" H 1400 4100 60  0001 L CNN
F 4 "609-4616-1-ND" H 1400 4200 60  0001 L CNN "Digi-Key_PN"
F 5 "10118193-0001LF" H 1400 4300 60  0001 L CNN "MPN"
F 6 "Connectors, Interconnects" H 1400 4400 60  0001 L CNN "Category"
F 7 "USB, DVI, HDMI Connectors" H 1400 4500 60  0001 L CNN "Family"
F 8 "http://www.amphenol-icc.com/media/wysiwyg/files/drawing/10118193.pdf" H 1400 4600 60  0001 L CNN "DK_Datasheet_Link"
F 9 "/product-detail/en/amphenol-icc-fci/10118193-0001LF/609-4616-1-ND/2785380" H 1400 4700 60  0001 L CNN "DK_Detail_Page"
F 10 "CONN RCPT USB2.0 MICRO B SMD R/A" H 1400 4800 60  0001 L CNN "Description"
F 11 "Amphenol ICC (FCI)" H 1400 4900 60  0001 L CNN "Manufacturer"
F 12 "Active" H 1400 5000 60  0001 L CNN "Status"
	1    1200 3800
	1    0    0    -1  
$EndComp
NoConn ~ 1500 3900
Wire Wire Line
	1500 3800 3300 3800
Wire Wire Line
	3300 3800 3300 2950
Wire Wire Line
	3300 2950 3850 2950
Wire Wire Line
	1500 3700 3850 3700
Wire Wire Line
	3050 4400 3050 4500
Wire Wire Line
	3050 3600 3050 4200
Wire Wire Line
	1500 3600 3050 3600
Wire Wire Line
	3050 4500 6900 4500
Connection ~ 3050 4500
Wire Wire Line
	3050 4500 3050 4600
Text Label 3500 2950 0    50   ~ 0
DP2
Text Label 3550 3700 0    50   ~ 0
DN2
Wire Wire Line
	4050 2950 6100 2950
Wire Wire Line
	6500 2100 6500 2600
Wire Wire Line
	5750 2100 6500 2100
Wire Wire Line
	6500 2800 6500 3800
Wire Wire Line
	6500 3800 3300 3800
Connection ~ 3300 3800
Wire Wire Line
	4000 2300 5350 2300
Wire Wire Line
	1550 1800 2950 1800
Wire Wire Line
	2950 1800 2950 2000
Wire Wire Line
	2950 2300 3800 2300
Wire Wire Line
	3450 1900 3450 1700
Wire Wire Line
	4000 1900 4400 1900
Wire Wire Line
	4400 1900 4400 2200
Wire Wire Line
	4400 2200 5350 2200
Wire Wire Line
	4650 2100 4500 2100
Wire Wire Line
	4500 2100 4500 2000
Wire Wire Line
	4500 2000 2950 2000
Connection ~ 2950 2000
Wire Wire Line
	2950 2000 2950 2300
Text Label 1950 3600 0    50   ~ 0
VBUS2
Wire Wire Line
	1150 2400 1150 2550
Wire Wire Line
	1150 2550 1800 2550
Wire Wire Line
	1800 2000 1800 2550
Connection ~ 1800 2550
Wire Wire Line
	1800 2550 1800 2650
$Comp
L power:GND #PWR0106
U 1 1 5C8503E8
P 1750 4650
F 0 "#PWR0106" H 1750 4400 50  0001 C CNN
F 1 "GND" H 1755 4477 50  0000 C CNN
F 2 "" H 1750 4650 50  0001 C CNN
F 3 "" H 1750 4650 50  0001 C CNN
	1    1750 4650
	1    0    0    -1  
$EndComp
Wire Wire Line
	1500 4000 1750 4000
Wire Wire Line
	1100 4550 1750 4550
Wire Wire Line
	1750 4000 1750 4550
Connection ~ 1750 4550
Wire Wire Line
	1750 4550 1750 4650
Wire Wire Line
	1100 4400 1100 4550
$EndSCHEMATC
