# FIXME: ensures bbl is always up to date, as bootloader does not auto update after changes
echo "Recreating bbl with payload"
make -C $1/.. riscv-pk-rebuild
