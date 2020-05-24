VER                 = 2016.1
VIVADO_SOURCE_CMDS  = -source scripts/setup.tcl -source scripts/synthesize.tcl

ifeq ($(VIVADO),)
VIVADO := vivado-${VER} vivado
endif

nogui: synth_nogui

gui: synth_gui

synth_nogui:
	${VIVADO} -mode batch $(VIVADO_SOURCE_CMDS)

synth_gui:
	${VIVADO} -mode gui $(VIVADO_SOURCE_CMDS)

clean:
	@rm -f *.jou *.log vivado_*.str
	@rm -rf vivado.*

