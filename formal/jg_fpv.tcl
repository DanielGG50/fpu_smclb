clear -all

#

# Flags
#analyze -sv ../rtl/flags_block.v

# Add Sub
#analyze -sv ../rtl/normalize_rounder.v
#analyze -sv ../rtl/mantissa_add_sub.v
analyze -sv ../rtl/mantissa_shifter.v 
#analyze -sv ../rtl/exponent_sub_upd.v
#analyze -sv ../rtl/sign_logic.v
#analyze -sv ../rtl/exception_block.v
#analyze -sv ../rtl/add_sub_main.v
 
#FV
analyze -sv mantissa_shifter_fv.sv
#analyze -sv mantissa_add_sub_fv.sv
#analyze -sv exception_block_fv.sv

#REMEMBER TO CHAMGE TOP WHEN TESTING INDIVIDUAL MODULES
elaborate -bbox_a 65535 -bbox_mul 65535 -top mantissa_shifter

clock clk

reset -expression !arst_n
set_engineJ_max_trace_length 5000
