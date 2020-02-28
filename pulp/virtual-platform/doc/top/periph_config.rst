.. _device_config:

Device configuration
====================

When using a simulation platform, the default configuration is usually only activating very few peripherals and
additional peripherals can be added by customizing the default configuration with a specific section in the user configuration.

The devices to be simulated must be specified in the user INI configuration (the one passed through option *-\\-config-user*). A section with name *board.devices.<device>* must be added for each device. <device> is the name of the peripheral in the architecture and can be anything as soon as it is different from other devices.

Each device section must at least have the property *include*, which specifies which device to be simulated. The rest is specific to each device.

When adding new devices, it may also be required to add other options for example to change the boot mode as the runner may need to generate different stimuli. These options are chip-specific.

Here is an example connecting an hyperflash and hyperram, and changing the boot mode: ::

  [board.devices.hyper]
  include = devices/hyper.json
  interface = hyper0
  cs = 0
  
  [config.runner]
  runner.boot-mode = rom_hyper
  runner.flash_type = hyper

Here is another example to connect 2 SPI flash: ::

  [board.devices.spiflash0]
  include = devices/spiflash.json
  interface = spim0
  cs = 0
  
  [board.devices.spiflash1]
  include = devices/spiflash.json
  interface = spim0
  cs = 1

The list of available devices can be displayed by using the command *devices* with *pulp-run* like in the following example: ::

  pulp-run --platform=gvsoc --config=gap_rev1 --binary=test devices

More information about a device can then be displayed by adding the option *-\\-device=<name>* where <name> is the name of the device taken from the table displayed with the command *devices*.
