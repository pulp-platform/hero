# FIXME: ensures bbl is always up to date, as bootloader does not auto update after changes
echo "Recreating bbl with payload"
make -C ${BASE_DIR} riscv-pk-rebuild
