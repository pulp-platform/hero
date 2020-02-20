#Create Folders 
set systemTime [clock seconds]
set UNIQUE_ID  [clock format $systemTime -format {%d_%B_%Y__%H_%M_%S}]

if { [file exists Backup] == 0} {               
          file mkdir ./Backup
}

set  BACKUP_FOLDER "Backup/$UNIQUE_ID"
file mkdir ./$BACKUP_FOLDER

proc create_folder {FOLDER_NAME BACKUP_FOLDER} {
	if { [file exists $FOLDER_NAME] == 0} {               
          file mkdir ./$FOLDER_NAME
    	} else {
    		sh mv $FOLDER_NAME $BACKUP_FOLDER
    		file mkdir ./$FOLDER_NAME
    	}
}

set folder_list [list export mapped unmapped reports ]
#set file_list   [list synth.log]

foreach item $folder_list {
	create_folder $item $BACKUP_FOLDER
}

# foreach item $file_list {
# 	if { [file exists $item] == 1} {  sh mv $item ./$BACKUP_FOLDER }
# }
