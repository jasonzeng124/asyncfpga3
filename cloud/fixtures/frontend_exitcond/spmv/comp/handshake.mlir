module {
  handshake.func @spmv(%arg0: !handshake.channel<i32>, %arg1: memref<11xi32>, %arg2: memref<10xi32>, %arg3: memref<10xi32>, %arg4: memref<10xi32>, %arg5: memref<10xi32>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, %arg8: !handshake.control<>, %arg9: !handshake.control<>, %arg10: !handshake.control<>, %arg11: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["n", "row", "col", "val", "vec", "out", "row_start", "col_start", "val_start", "vec_start", "out_start", "start"], resNames = ["out0", "row_end", "col_end", "val_end", "vec_end", "out_end", "end"]} {
    %memEnd = mem_controller[%arg5 : memref<10xi32>] %arg10 (%28, %addressResult_49, %dataResult_50) %result_59 {connectedBlocks = [3 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> ()
    %outputs, %memEnd_0 = mem_controller[%arg4 : memref<10xi32>] %arg9 (%addressResult_31) %result_59 {connectedBlocks = [2 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_1, %memEnd_2 = mem_controller[%arg3 : memref<10xi32>] %arg8 (%addressResult_27) %result_59 {connectedBlocks = [2 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_3, %memEnd_4 = mem_controller[%arg2 : memref<10xi32>] %arg7 (%addressResult_29) %result_59 {connectedBlocks = [2 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_5:2, %memEnd_6 = mem_controller[%arg1 : memref<11xi32>] %arg6 (%addressResult, %addressResult_11) %result_59 {connectedBlocks = [1 : i32], handshake.name = "mem_controller4"} :    (!handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %0 = constant %arg11 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = cmpi sgt, %arg0, %0 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %1, %0 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_7, %falseResult_8 = cond_br %1, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_9, %falseResult_10 = cond_br %1, %arg11 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %2 = mux %index [%trueResult, %trueResult_51] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %3 = mux %index [%trueResult_7, %trueResult_53] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_9, %trueResult_55]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %4 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %5 = constant %4 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %6 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 0 : i32} : <>, <i32>
    %7 = extui %2 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %8 = trunci %7 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%8] %outputs_5#0 {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %9 = addi %2, %5 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %10 = extui %9 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %11 = trunci %10 {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_11, %dataResult_12 = load[%11] %outputs_5#1 {handshake.bb = 1 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %12 = cmpi slt, %dataResult, %dataResult_12 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_13, %falseResult_14 = cond_br %12, %dataResult {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_15, %falseResult_16 = cond_br %12, %6 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_17, %falseResult_18 = cond_br %12, %3 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_19, %falseResult_20 = cond_br %12, %2 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_21, %falseResult_22 = cond_br %12, %dataResult_12 {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_23, %falseResult_24 = cond_br %12, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br12"} : <i1>, <>
    %13 = mux %index_26 [%trueResult_13, %trueResult_33] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %14 = mux %index_26 [%trueResult_15, %trueResult_35] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %15 = mux %index_26 [%trueResult_17, %trueResult_37] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %16 = mux %index_26 [%trueResult_19, %trueResult_39] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %17 = mux %index_26 [%trueResult_13, %trueResult_41] {handshake.bb = 2 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %18 = mux %index_26 [%trueResult_21, %trueResult_43] {handshake.bb = 2 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %result_25, %index_26 = control_merge [%trueResult_23, %trueResult_45]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %19 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %20 = constant %19 {handshake.bb = 2 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %21 = trunci %13 {handshake.bb = 2 : ui32, handshake.name = "index_cast2"} : <i32> to <i32>
    %addressResult_27, %dataResult_28 = load[%21] %outputs_1 {handshake.bb = 2 : ui32, handshake.name = "load2"} : <i32>, <i32>, <i32>, <i32>
    %22 = trunci %13 {handshake.bb = 2 : ui32, handshake.name = "index_cast3"} : <i32> to <i32>
    %addressResult_29, %dataResult_30 = load[%22] %outputs_3 {handshake.bb = 2 : ui32, handshake.name = "load3"} : <i32>, <i32>, <i32>, <i32>
    %23 = trunci %dataResult_30 {handshake.bb = 2 : ui32, handshake.name = "index_cast4"} : <i32> to <i32>
    %addressResult_31, %dataResult_32 = load[%23] %outputs {handshake.bb = 2 : ui32, handshake.name = "load4"} : <i32>, <i32>, <i32>, <i32>
    %24 = muli %dataResult_28, %dataResult_32 {handshake.bb = 2 : ui32, handshake.name = "muli0"} : <i32>
    %25 = addi %14, %24 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %26 = addi %13, %20 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i32>
    %27 = cmpi ne, %26, %18 {handshake.bb = 2 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_33, %falseResult_34 = cond_br %27, %26 {handshake.bb = 2 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_35, %falseResult_36 = cond_br %27, %25 {handshake.bb = 2 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_37, %falseResult_38 = cond_br %27, %15 {handshake.bb = 2 : ui32, handshake.name = "cond_br15"} : <i1>, <i32>
    %trueResult_39, %falseResult_40 = cond_br %27, %16 {handshake.bb = 2 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    %trueResult_41, %falseResult_42 = cond_br %27, %17 {handshake.bb = 2 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    %trueResult_43, %falseResult_44 = cond_br %27, %18 {handshake.bb = 2 : ui32, handshake.name = "cond_br18"} : <i1>, <i32>
    %trueResult_45, %falseResult_46 = cond_br %27, %result_25 {handshake.bb = 2 : ui32, handshake.name = "cond_br19"} : <i1>, <>
    %28 = constant %result_47 {handshake.bb = 3 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %29 = mux %index_48 [%falseResult_16, %falseResult_36] {handshake.bb = 3 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %30 = mux %index_48 [%falseResult_18, %falseResult_38] {handshake.bb = 3 : ui32, handshake.name = "mux9"} : <i1>, [<i32>, <i32>] to <i32>
    %31 = mux %index_48 [%falseResult_20, %falseResult_40] {handshake.bb = 3 : ui32, handshake.name = "mux10"} : <i1>, [<i32>, <i32>] to <i32>
    %32 = mux %index_48 [%falseResult_14, %falseResult_42] {handshake.bb = 3 : ui32, handshake.name = "mux11"} : <i1>, [<i32>, <i32>] to <i32>
    %result_47, %index_48 = control_merge [%falseResult_24, %falseResult_46]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %33 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %34 = constant %33 {handshake.bb = 3 : ui32, handshake.name = "constant5", value = 1 : i32} : <>, <i32>
    %35 = extui %31 {handshake.bb = 3 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %36 = trunci %35 {handshake.bb = 3 : ui32, handshake.name = "index_cast5"} : <i64> to <i32>
    %addressResult_49, %dataResult_50 = store[%36] %29 {handshake.bb = 3 : ui32, handshake.name = "store5"} : <i32>, <i32>, <i32>, <i32>
    %37 = addi %31, %34 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i32>
    %38 = cmpi ne, %37, %30 {handshake.bb = 3 : ui32, handshake.name = "cmpi3"} : <i32>
    %trueResult_51, %falseResult_52 = cond_br %38, %37 {handshake.bb = 3 : ui32, handshake.name = "cond_br20"} : <i1>, <i32>
    %trueResult_53, %falseResult_54 = cond_br %38, %30 {handshake.bb = 3 : ui32, handshake.name = "cond_br21"} : <i1>, <i32>
    %trueResult_55, %falseResult_56 = cond_br %38, %result_47 {handshake.bb = 3 : ui32, handshake.name = "cond_br22"} : <i1>, <>
    %trueResult_57, %falseResult_58 = cond_br %38, %32 {handshake.bb = 3 : ui32, handshake.name = "cond_br23"} : <i1>, <i32>
    %39 = mux %index_60 [%falseResult, %falseResult_58] {handshake.bb = 4 : ui32, handshake.name = "mux12"} : <i1>, [<i32>, <i32>] to <i32>
    %result_59, %index_60 = control_merge [%falseResult_10, %falseResult_56]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %39, %memEnd_6, %memEnd_4, %memEnd_2, %memEnd_0, %memEnd, %arg11 : <i32>, <>, <>, <>, <>, <>, <>
  }
}

