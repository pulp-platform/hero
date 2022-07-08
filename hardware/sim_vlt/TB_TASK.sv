//-------------------------------------------------
// Test Vector Log
//-------------------------------------------------
task sv_log;
    input string str;

    $display("[TV_LOG] %0s", str);
endtask:sv_log
//-------------------------------------------------


//-------------------------------------------------
// SFR WRITE TASK DECLARE
//-------------------------------------------------
task write_word;
    input [31:0] ADDR;
    input [31:0] DATA;

    $display("write_word(0x%0x, 0x%0x)", ADDR, DATA);
    HOST.write32(ADDR, DATA);
    $display("word write complete");
endtask:write_word
//-------------------------------------------------


//-------------------------------------------------
// SFR READ TASK DECLARE
//-------------------------------------------------
task read_word;
    input [31:0] ADDR;
    output[31:0] DATA;

    $display("read_word(0x%0x)", ADDR);
    HOST.read32(ADDR, DATA);
    $display("   => 0x%0x", DATA);
    $display("word read complete");
endtask:read_word
//-------------------------------------------------

