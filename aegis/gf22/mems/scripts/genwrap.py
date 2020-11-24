import re
import sys
import math


SRAM_TEMPLATE = '''
        {0} i_{0} (
            .CLK         ( clk_i                      ),
            .CEN         ( ~req_i[0]                  ),
            .RDWEN       ( ~we_i[0]                   ),
            .AW          ( addr_i[0][AddrWidth-1:{1}+1] ),
            .AC          ( addr_i[0][{1}:0]             ),
            .D           ( wdata_i[0]                 ),
            .BW          ( bit_enable                 ),
            .T_LOGIC     ( 1'b0                       ),
            .MA_SAWL     ( '0                         ),
            .MA_WL       ( '0                         ),
            .MA_WRAS     ( '0                         ),
            .MA_WRASD    ( '0                         ),
            .Q           ( rdata_o[0]                 ),
            .OBSV_CTL    (                            )
        );
'''


BLOCK_TEMPLATE = '''    {0}(NumWords == {1} & DataWidth == {2}) begin : gen_NW{1}_DW{2}'''

MEM_REGEX = r'IN22FDX_R1PH_NFHN_W([0-9]+)B([0-9]+)M([0-9]+)C([0-9]+)'

# read template
template_string = open(sys.argv[1], 'r').read()

# read the report file and put the wrapper together
srams = ''
first = True
no_macro = True

# get the needed sram names from invoking the get_sram_names on the
if len(sys.argv) > 2:
    report_file_name = sys.argv[2]
    # get missing sram names
    sram_names = open(report_file_name, 'r').read().split()
    # break of no srams are missing
    if len(sram_names) > 0:
        # add instances in wrapper
        for sram in sram_names:
            parsed_descr = re.findall(MEM_REGEX, sram)[0]
            mux_width = math.ceil(math.log(int(parsed_descr[2]), 2)) - 1
            if first:
                srams += BLOCK_TEMPLATE.format('if ', *parsed_descr[0:2])
                srams += SRAM_TEMPLATE.format(sram, mux_width)
                srams += '    end\n'
                first = False
            else:
                srams += BLOCK_TEMPLATE.format('else if', *parsed_descr[0:2])
                srams += SRAM_TEMPLATE.format(sram, mux_width)
                srams += '    end\n'
        # finally: write blackbox. else cause is needed only if no report file is specified
        srams += '    else begin : gen_tc_sram_blackbox'
        srams += SRAM_TEMPLATE.format('tc_sram_blackbox', 0)
        srams += '    end'
        # at least one macro is in wrapper
        no_macro = False

if no_macro:
    # if no macro was found -> just instantiate blackbox
    srams += SRAM_TEMPLATE.format('tc_sram_blackbox', 0)

print(template_string.format(srams))
