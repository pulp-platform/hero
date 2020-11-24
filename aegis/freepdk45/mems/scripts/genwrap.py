import re
import sys


SRAM_TEMPLATE = '''
        {0} i_{0} (
            .clk0   ( clk_i    ),
            .csb0   ( ~req_i   ),
            .web0   ( ~we_i    ),
            .wmask0 ( be_i     ),
            .addr0  ( addr_i   ),
            .din0   ( wdata_i  ),
            .dout0  ( rdata_o  )
        );
'''

DP_SRAM_TEMPLATE = '''
        {0} i_{0} (
            .clk0   ( clk_i        ),
            .csb0   ( ~req_i  [0]  ),
            .web0   ( ~we_i   [0]  ),
            .wmask0 ( be_i    [0]  ),
            .addr0  ( addr_i  [0]  ),
            .din0   ( wdata_i [0]  ),
            .dout0  ( rdata_o [0]  ),

            .clk1   ( clk_i        ),
            .csb1   ( ~req_i  [1]  ),
            .web1   ( ~we_i   [1]  ),
            .wmask1 ( be_i    [1]  ),
            .addr1  ( addr_i  [1]  ),
            .din1   ( wdata_i [1]  ),
            .dout1  ( rdata_o [1]  )
        );
'''

BLOCK_TEMPLATE = '''    {0}(NumWords == {1} & DataWidth == {2} & ByteWidth == {3} & NumPorts == {4}) begin : gen_NW{1}_DW{2}_BW{3}_NP{4}'''

MEM_REGEX = r'openram_sram_D([0-9]+)_W([0-9]+)_B([0-9]+)_P([0-9]+)_freepdk45'


# read template
template_string = open(sys.argv[1], 'r').read()

# read the report file and put the wrapper together
srams = ''
first = True
no_macro = True

# get the needed sram names from invoking the get_sram_names on the
# report file (argv[2])
if len(sys.argv) > 2:
    report_file_name = sys.argv[2]
    # get missing sram names
    sram_names = open(report_file_name, 'r').read().split()
    # break of no srams are missing
    if len(sram_names) > 0:
        # add instances in wrapper
        for sram in sram_names:
            parsed_descr = re.findall(MEM_REGEX, sram)[0]
            if first:
                srams += BLOCK_TEMPLATE.format('if ', *parsed_descr[0:4])
                if (parsed_descr[3] == '1'):
                    srams += SRAM_TEMPLATE.format(sram)
                elif (parsed_descr[3] == '2'):
                    srams += DP_SRAM_TEMPLATE.format(sram)
                else:
                    print("Only one or two ports supported!", file=sys.stderr)
                    sys.exit(-1)
                srams += '    end\n'
                first = False
            else:
                srams += BLOCK_TEMPLATE.format('else if', *parsed_descr[0:4])
                if (parsed_descr[3] == '1'):
                    srams += SRAM_TEMPLATE.format(sram)
                elif (parsed_descr[3] == '2'):
                    srams += DP_SRAM_TEMPLATE.format(sram)
                else:
                    print("Only one or two ports supported!", file=sys.stderr)
                    sys.exit(-1)
                srams += '    end\n'
        # finally: write blackbox. else cause is needed only if no report file is specified
        srams += '    else begin : gen_tc_sram_blackbox'
        srams += SRAM_TEMPLATE.format('tc_sram_blackbox')
        srams += '    end'
        # at least one macro is in wrapper
        no_macro = False

if no_macro:
    # if no macro was found -> just instantiate blackbox
    srams += SRAM_TEMPLATE.format('tc_sram_blackbox')

print(template_string.format(srams))
