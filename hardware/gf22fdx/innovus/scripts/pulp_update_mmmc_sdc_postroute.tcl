create_constraint_mode -name func_mode \
            -sdc_files [list src/constraints/PostRoute/constraints_mode0.sdc \
                       ]

# Specify analysis views to use
set_analysis_view -setup { view_ssg_M40C_Cmax view_ssg_M40C_RCmax view_ssg_125C_Cmax view_ssg_125C_RCmax } \
                  -hold  { view_ffg_M40C_Cmin view_ffg_M40C_RCmin view_ffg_125C_Cmin view_ffg_125C_RCmin }

set_analysis_view -update_timing