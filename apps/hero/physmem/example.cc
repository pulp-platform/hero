#include "physmem.hpp"

int main() {
  PhysMem mem(0xA0000000, 0x10000000);

  std::cout << std::hex
    << "0x" << mem.read_u32(0xA8000040) << std::endl
    << "0x" << mem.read_u32(0xA8000048) << std::endl
    << "0x" << mem.read_u32(0xA8000050) << std::endl
    << "0x" << mem.read_u32(0xA8000058) << std::endl;
  return 0;
}
