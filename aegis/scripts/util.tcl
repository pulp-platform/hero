# Colors
set CBLACK   [exec tput -Txterm-color setaf 0]
set CRED     [exec tput -Txterm-color setaf 1]
set CGREEN   [exec tput -Txterm-color setaf 2]
set CYELLOW  [exec tput -Txterm-color setaf 3]
set CBLUE    [exec tput -Txterm-color setaf 4]
set CMAGENTA [exec tput -Txterm-color setaf 5]
set CCYAN    [exec tput -Txterm-color setaf 6]
set CWHITE   [exec tput -Txterm-color setaf 7]
set CBOLD    [exec tput -Txterm-color bold]
set CRST     [exec tput -Txterm-color sgr0]

# Highlighted output
proc puts_pass {msg} {
    global CBOLD CGREEN CRST
    puts "${CBOLD}${CGREEN}${msg}${CRST}"
}

proc puts_warn {msg} {
    global CBOLD CYELLOW CRST
    puts "${CBOLD}${CYELLOW}${msg}${CRST}"
}

proc puts_fail {msg} {
    global CBOLD CRED CRST
    puts "${CBOLD}${CRED}${msg}${CRST}"
}

proc puts_log {msg} {
    global CBOLD CCYAN CRST
    puts "${CBOLD}${CCYAN}${msg}${CRST}"
}

# check if error occurred; if so, inform and run handler command
proc on_error_occurred {cmd_name cmd_output handler {error_str "Error: "}} {
    set cmd_errors [regexp ${error_str} $cmd_output]
    puts $cmd_output
    if $cmd_errors {
        puts_fail "${cmd_name} encountered errors"
        eval ${handler}
    } else {
        puts_pass "${cmd_name} successful"
    }
    return $cmd_errors
}

proc set_if_undef {varname default} {
    upvar $varname _varname
    set _varname [expr {[info exists _varname] ? $_varname : $default}]
}
