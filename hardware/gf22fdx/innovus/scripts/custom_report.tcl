proc custom_report { args } {
    global rdagEffectiveDensity

    # Parse options
    set index 0
    set help false
    set outputFile {}
    foreach arg $args {
        incr index
        switch -exact -- $arg {
            "-output" { set outputFile [lindex $args $index] }
            "-help"   { set help       true                  }
        }
    }

    # Check options
    if { $help } then {
    #    puts $outputFileId "Usage: ::stm::PRSummary (Customized PRSummary)"
    #    puts $outputFileId "         -output <string>: Output file name"
        return ""
    }
    if { ![info exists outputFile] } then {
    #    puts $outputFileId "REPORT: missing -output"
        return 0
    }

    set outputFileId [open $outputFile "w"]

    #
    # Get area and utilization numbers
    #
    set corebox [dbFPlanCoreBox [dbHeadFPlan]]
    set llx [expr [lindex $corebox 0]*[dbHeadMicronPerDBU]]
    set lly [expr [lindex $corebox 1]*[dbHeadMicronPerDBU]]
    set urx [expr [lindex $corebox 2]*[dbHeadMicronPerDBU]]
    set ury [expr [lindex $corebox 3]*[dbHeadMicronPerDBU]]
    set corewidth [expr $urx - $llx]
    set coreheight [expr $ury - $lly]
    set corearea [expr $corewidth * $coreheight]

    set chipbox [dbHeadBox [dbgHead]]
    set llx [expr [lindex $chipbox 0]*[dbHeadMicronPerDBU]]
    set lly [expr [lindex $chipbox 1]*[dbHeadMicronPerDBU]]
    set urx [expr [lindex $chipbox 2]*[dbHeadMicronPerDBU]]
    set ury [expr [lindex $chipbox 3]*[dbHeadMicronPerDBU]]
    set chipwidth [expr $urx - $llx]
    set chipheight [expr $ury - $lly]
    set chiparea [expr $chipwidth * $chipheight]
    set rowNumber [dbFPlanNrRow [dbHeadFPlan]]
    eval queryPlaceDensity
    set effective_utilization $rdagEffectiveDensity

    #
    # Get Module Information
    #
#    puts $outputFileId "REPORT: Analyzing Floorplan"
    set instanceNumber 0
    set svtInstanceNumber 0
    set svtString "SVT"

    set hvtCellNumber 0
    set lvtCellNumber 0
    set rvtCellNumber 0

    set hvtCellArea 0
    set lvtCellArea 0
    set rvtCellArea 0

    set macroNumber 0
    set stdNumber 0
    set ioNumber 0
    set fillerNumber 0
    set ioFillerNumber 0
    set macroArea 0
    set stdArea 0
    set ioArea 0
    set flipFlopNumber 0
    set pinInstNumber 0
    array set cellInstArray [list]
    array set cellTypeArray [list]
    set coreFillerCells [findCoreFillerCells]
    dbForEachCellInst [dbgTopCell] instPtr {
        incr instanceNumber
        set masterName [dbCellName [dbInstCell $instPtr]]
        if { [dbIsInstBlock $instPtr] } then {
            incr macroNumber
            set cellTypeArray($masterName) MACRO
            set macroArea [expr ($macroArea + (([lindex [dbCellDim [dbInstCell $instPtr]] 0] * [dbHeadMicronPerDBU]) * ([lindex [dbCellDim [dbInstCell $instPtr]] 1] * [dbHeadMicronPerDBU])))]
        } elseif { [dbIsInstStdCell $instPtr] } then {
            if { (![string equal {fill_} [string range [dbInstName $instPtr] 0 4]]) && (![string equal {WELLTAP} [string range [dbInstName $instPtr] 0 5]]) && ([lsearch $coreFillerCells $masterName] == -1) } then {
                incr stdNumber
                set cellTypeArray($masterName) STD
		set instArea [expr (([lindex [dbCellDim [dbInstCell $instPtr]] 0] * [dbHeadMicronPerDBU]) * ([lindex [dbCellDim [dbInstCell $instPtr]] 1] * [dbHeadMicronPerDBU]))]
                set stdArea [expr ($stdArea + $instArea)]
		if { [string match *WA $masterName] || [string match *W $masterName] } {
			incr  lvtCellNumber
			set lvtCellArea [expr $lvtCellArea + $instArea]
		} elseif { [string match *SA $masterName] || [string match *S $masterName] } {
			incr  hvtCellNumber
			set hvtCellArea [expr $hvtCellArea + $instArea]
		} else {
			incr  rvtCellNumber
			set rvtCellArea [expr $rvtCellArea + $instArea]
		}
                if { [dbIsCellSequential [dbInstCell $instPtr]] } then { incr flipFlopNumber }
            } else {
                incr fillerNumber
                set cellTypeArray($masterName) FILLER
            }
        } elseif { [dbIsInstIo $instPtr] } then {
            if { ![string match IFILL* $masterName] } then {
                incr ioNumber
                set cellTypeArray($masterName) PAD
                set ioArea [expr ($ioArea + (([lindex [dbCellDim [dbInstCell $instPtr]] 0] * [dbHeadMicronPerDBU]) * ([lindex [dbCellDim [dbInstCell $instPtr]] 1] * [dbHeadMicronPerDBU])))]
            } else {
                incr ioFillerNumber
                set cellTypeArray($masterName) IOFILLER
            }
        }
        set pinInstNumber [expr ($pinInstNumber + [dbCellNrFTerm [dbInstCell $instPtr]])]
        if { [info exist cellInstArray($masterName)] } then {
            incr cellInstArray($masterName)
        } else {
            set cellInstArray($masterName) 1
        }
    }
    set listInstStd [list]
    set listInstMacro [list]
    set listInstFiller [list]
    set listInstIo [list]
    foreach k [array names cellInstArray] {
        if { $cellTypeArray($k) == "STD" } then {
            set listInstStd [lappend listInstStd [list $k $cellTypeArray($k) $cellInstArray($k)]]
        } elseif { $cellTypeArray($k) == "MACRO" } then {
            set listInstMacro [lappend listInstMacro [list $k $cellTypeArray($k) $cellInstArray($k)]]
        } elseif { $cellTypeArray($k) == "PAD" } then {
            set listInstIo [lappend listInstIo [list $k $cellTypeArray($k) $cellInstArray($k)]]
        } else {
            set listInstFiller [lappend listInstFiller [list $k $cellTypeArray($k) $cellInstArray($k)]]
        }
    }
    set listInstStd [lsort -decreasing -integer -index 2 $listInstStd]
    set listInstMacro [lsort -decreasing -integer -index 2 $listInstMacro]
    set listInstFiller [lsort -decreasing -integer -index 2 $listInstFiller]
    set listInst [concat $listInstStd $listInstMacro $listInstIo $listInstFiller]
    foreach element $listInst {
        if {[regexp $svtString [lindex $element 0]]} {
            set svtInstanceNumber [expr ($svtInstanceNumber + [lindex $element 2])]
        }
    }
    set fTermNumber [dbCellNrFTerm [dbgTopCell]]

    #
    # Get net statistics
    #
#    puts $outputFileId "REPORT: Analyzing Signal/Power Wires"
    set netNumber 0
    set internalNetNumber 0
    set externalNetNumber 0
    set specialNetNumber 0
    set horizontalInternalNetLength 0
    set verticalInternalNetLength 0
    set termNumber 0
    array set listeLayerArray [list]
    array set verticalWireLengthArray [list]
    array set horizontalWireLengthArray [list]
    array set verticalWireNumberArray [list]
    array set horizontalWireNumberArray [list]

    array set listeViaArray [list]
    array set listeViaNumberArray [list]

    array set stripeListeLayerArray [list]
    array set stripeWireLengthArray [list]
    array set stripeWireNumberArray [list]

    array set stripeListeViaArray [list]
    array set stripeViaNumberArray [list]

    array set followPinListeLayerArray [list]
    array set followPinWireLengthArray [list]
    array set followPinWireNumberArray [list]

    array set followPinListeViaArray [list]
    array set followPinViaNumberArray [list]

    puts $outputFileId "REPORT: Writing Statistics"
    puts $outputFileId "****************************** P&R Summary ********************************"
    puts $outputFileId "Date             : [clock format [clock seconds]]"
    puts $outputFileId "Machine Host Name: [info hostname]"
    puts $outputFileId "Working Directory: [pwd]"
    #puts $outputFileId "Library Name:      lib_[dbCellName [dbgTopCell]]_work"
    puts $outputFileId "Cell Name:         [dbCellName [dbgTopCell]]"
    puts $outputFileId ""
    puts $outputFileId "Design Statistics:"
    puts $outputFileId "    Number of Macro Cells:         $macroNumber"
    puts $outputFileId "    Number of Pads Cells:          $ioNumber"
    puts $outputFileId "    Number of Std Cells:           $stdNumber"
    puts $outputFileId "            RVT:                   $rvtCellNumber\([format \"%.2f\" [expr ($rvtCellNumber*100.0/$stdNumber)]]%\) area $rvtCellArea\([format \"%.2f\" [expr ($rvtCellArea*100.0/$stdArea)]]%\)"
    puts $outputFileId "            HVT:                   $hvtCellNumber\([format \"%.2f\" [expr ($hvtCellNumber*100.0/$stdNumber)]]%\) area $hvtCellArea\([format \"%.2f\" [expr ($hvtCellArea*100.0/$stdArea)]]%\)"
    puts $outputFileId "            LVT:                   $lvtCellNumber\([format \"%.2f\" [expr ($lvtCellNumber*100.0/$stdNumber)]]%\) area $lvtCellArea\([format \"%.2f\" [expr ($lvtCellArea*100.0/$stdArea)]]%\)"
    puts $outputFileId "    Number of Filler Cells:        $fillerNumber"
    puts $outputFileId "    Number of Filler Pads:         $ioFillerNumber"
    puts $outputFileId "    Number of Flops:               $flipFlopNumber ([format \"%.2f\" [expr ($flipFlopNumber*100.0/$stdNumber)]]%)"
#    puts $outputFileId "    Number of SVT Cells:           $svtInstanceNumber ([format \"%.2f\" [expr ($svtInstanceNumber*100.0/$stdNumber)]]%)"
    puts $outputFileId "    Number of Pins (instance):     $pinInstNumber"
    puts $outputFileId "    Number of Terminal (net):      $termNumber"
    puts $outputFileId "    Number of IO Pins:             $fTermNumber"
    puts $outputFileId "    Number of Nets:                $internalNetNumber"
#    puts $outputFileId "    Average Pins Per Net (Signal): [format \"%.2f\" [expr ($termNumber * 1.0 / $internalNetNumber )]]"
    puts $outputFileId ""
    puts $outputFileId "Chip Utilization:"
    puts $outputFileId "    Total Macro Cell Area:         [format \"%.2f\" $macroArea]"
    puts $outputFileId "    Total Standard Cell Area:      [format \"%.2f\" $stdArea]"
    puts $outputFileId "    Core Size:     width [format \"%.2f\" $corewidth], height [format \"%.2f\" $coreheight]; area [format \"%.2f\" $corearea]"
    puts $outputFileId "    Chip Size:     width [format \"%.2f\" $chipwidth], height [format \"%.2f\" $chipheight]; area [format \"%.2f\" $chiparea]"
    puts $outputFileId "    Cell/Core Ratio:               [format \"%.4f\" [expr (100.0 * (($macroArea + $stdArea)/$corearea))]]%"
    puts $outputFileId "    Cell/Chip Ratio:               [format \"%.4f\" [expr (100.0 * (($macroArea + $stdArea)/$chiparea))]]%"
    puts $outputFileId "    Encounter Density:             [format \"%.4f\" [expr (100.0 * $effective_utilization)]]%"
    puts $outputFileId "    Number of Cell Rows:           $rowNumber"

    #
    # Instance Informations
    #
    puts $outputFileId ""
    puts $outputFileId "Master Instantiation:"
    puts $outputFileId [format "        %-30s%-5s   %s" "MasterName" "Type" "InstCount"]
    puts $outputFileId "        ================================================"
    foreach element $listInst {
        puts $outputFileId [format "        %-30s%-8s   %d" [lindex $element 0] [lindex $element 1] [lindex $element 2]]
    }
    puts $outputFileId "        ================================================"
    puts $outputFileId ""
    close $outputFileId
}

