import argparse
import json
import gspread
import os
from datetime import datetime
from oauth2client.service_account import ServiceAccountCredentials
import parsesynde

parser = argparse.ArgumentParser(description='Upload to google docs for Aegis')
parser.add_argument('aegis_json', type=str, help='the aegis json containing the tests')
parser.add_argument('test_name', type=str, help='the test to execute')
parser.add_argument('commit', type=str, help='the git commit')
args = parser.parse_args()

with open(args.aegis_json) as file:
    design = json.load(file)['gtable'][args.test_name]

# synopsys report directory
synde_rpt_dir = os.path.abspath(os.path.expandvars(design['synde_rpt_dir']))

parsed_rpt = parsesynde.synde_parse(synde_rpt_dir)

# use creds to create a client to interact with the Google Drive API
scopes = ['https://www.googleapis.com/auth/spreadsheets', 'https://www.googleapis.com/auth/drive.file', \
'https://www.googleapis.com/auth/drive', 'https://spreadsheets.google.com/feeds']

print(design['gapi_key'])

creds = ServiceAccountCredentials.from_json_keyfile_name(design['gapi_key'], scopes)
client = gspread.authorize(creds)

# open sheet
sheet = client.open(design['table_name']).worksheet(args.test_name)

# find next free entry and upload data
current_entry = len(sheet.col_values(1)[0:]) + 1

sheet.update_cell(current_entry, 1, datetime.now().strftime("%d.%m.%Y %H:%M:%S"))
sheet.update_cell(current_entry, 2, args.commit)

# area
sheet.update_cell(current_entry, 3, parsed_rpt['area']['Combinational area'] / design['kge_conversion'])
sheet.update_cell(current_entry, 4, parsed_rpt['area']['Buf/Inv area'] / design['kge_conversion'])
sheet.update_cell(current_entry, 5, parsed_rpt['area']['Noncombinational area'] / design['kge_conversion'])
sheet.update_cell(current_entry, 6, parsed_rpt['area']['Macro/Black Box area'] / design['kge_conversion'])
sheet.update_cell(current_entry, 7, parsed_rpt['area']['Total cell area'] / design['kge_conversion'])

#qor
sheet.update_cell(current_entry,  8, parsed_rpt['qor']['Levels of Logic'])
sheet.update_cell(current_entry,  9, 1000.0 / parsed_rpt['qor']['Critical Path Length'])
sheet.update_cell(current_entry, 10, 1000.0 / parsed_rpt['qor']['Critical Path Clk Period'])

#path
path_eles = []
for ele in parsed_rpt['timing']['paths'][0]['elems']:
    path_eles.append(str(ele._asdict()['point']))
sheet.update_cell(current_entry,  11,  ' <---> '.join(path_eles))

