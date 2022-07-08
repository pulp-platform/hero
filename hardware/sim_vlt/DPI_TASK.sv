//------------------------------------------------- 
// preload memory
//------------------------------------------------- 
export "DPI-C" task preload_mem_dpi;

task preload_mem_dpi;
    input   string file_name;
    input   int    addr;

    $display("preaload data to external memory");
    EXT_MEMORY.BIN_PRELOAD(addr, file_name);
endtask:preload_mem_dpi
//------------------------------------------------- 


//------------------------------------------------ 
// call write_word task from c-codes
//------------------------------------------------- 
export "DPI-C" task write_word_dpi;

task write_word_dpi;
    input int addr;
    input int data;

    write_word(addr, data);
endtask:write_word_dpi
//------------------------------------------------- 


//------------------------------------------------- 
// call read_word task from c-codes
//------------------------------------------------- 
export "DPI-C" task read_word_dpi;

task read_word_dpi;
    input  int addr;
    output int data;

    read_word(addr, data);
endtask:read_word_dpi
//------------------------------------------------- 

