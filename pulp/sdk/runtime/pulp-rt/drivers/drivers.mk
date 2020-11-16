
#
# DRIVERS
#


# PADS
ifeq '$(CONFIG_PADS_ENABLED)' '1'
ifneq '$(padframe/version)' ''
PULP_LIB_FC_SRCS_rt += drivers/pads/pads-v$(padframe/version).c
endif
endif


# SPIM

ifeq '$(CONFIG_SPIM_ENABLED)' '1'
ifneq '$(soc/spi_master)' ''
PULP_LIB_FC_SRCS_rt += drivers/spim/spim-v0.c
endif

ifneq '$(udma/spim)' ''
PULP_LIB_FC_SRCS_rt += drivers/spim/spim-v$(udma/spim/version).c drivers/spim/spiflash-v$(udma/spim/version).c
endif
endif


# HYPER

ifeq '$(CONFIG_HYPER_ENABLED)' '1'
ifneq '$(udma/hyper)' ''
PULP_LIB_FC_SRCS_rt += drivers/hyper/hyperram.c drivers/hyper/hyperflash.c
endif
endif


# UART

ifeq '$(CONFIG_UART_ENABLED)' '1'
ifneq '$(udma/uart)' ''
PULP_LIB_FC_SRCS_rt += drivers/uart/uart.c
endif

ifneq '$(soc/apb_uart)' ''
PULP_LIB_FC_SRCS_rt += drivers/uart/uart-v0.c
endif
endif


# I2S

ifeq '$(CONFIG_I2S_ENABLED)' '1'
ifneq '$(udma/i2s)' ''
PULP_LIB_FC_SRCS_rt += drivers/i2s/i2s.c
endif
endif


# CAM

ifeq '$(CONFIG_CAM_ENABLED)' '1'
ifneq '$(udma/cpi)' ''
PULP_LIB_FC_SRCS_rt += drivers/camera/himax.c drivers/camera/ov7670.c drivers/camera/camera.c
endif
endif


# I2C

ifeq '$(CONFIG_I2C_ENABLED)' '1'
ifneq '$(udma/i2c/version)' ''
PULP_LIB_FC_SRCS_rt += drivers/i2c/i2c-v$(udma/i2c/version).c
endif
endif


# RTC

ifeq '$(CONFIG_RTC_ENABLED)' '1'
ifneq '$(rtc)' ''
PULP_LIB_FC_SRCS_rt += drivers/dolphin/rtc.c
PULP_LIB_FC_ASM_SRCS_rt += drivers/dolphin/rtc_asm.S
endif
endif


# GPIO

ifeq '$(CONFIG_GPIO_ENABLED)' '1'
ifneq '$(gpio/version)' ''
PULP_LIB_FC_SRCS_rt += drivers/gpio/gpio-v$(gpio/version).c
ifeq '$(gpio/version)' '2'
PULP_LIB_FC_ASM_SRCS_rt += kernel/riscv/gpio.S
endif
endif
endif






ifeq '$(CONFIG_FLASH_FS_ENABLED)' '1'
PULP_LIB_FC_SRCS_rt += drivers/flash.c drivers/read_fs.c
endif