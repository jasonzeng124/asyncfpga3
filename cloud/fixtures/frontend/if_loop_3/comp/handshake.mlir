module {
  handshake.func @if_loop_3(%arg0: memref<100xi32>, %arg1: memref<100xi32>, %arg2: !handshake.channel<i32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "n", "a_start", "b_start", "start"], resNames = ["out0", "a_end", "b_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg1 : memref<100xi32>] %arg4 (%addressResult_8) %result_32 {connectedBlocks = [1 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_0, %memEnd_1 = mem_controller[%arg0 : memref<100xi32>] %arg3 (%addressResult) %result_32 {connectedBlocks = [1 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %0 = constant %arg5 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = constant %arg5 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 1000 : i32} : <>, <i32>
    %2 = cmpi sgt, %arg2, %0 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %2, %0 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %2, %1 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %2, %arg2 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %2, %arg5 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %3 = mux %index [%trueResult, %trueResult_24] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %4 = mux %index [%trueResult_2, %trueResult_26] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %5 = mux %index [%trueResult_4, %trueResult_28] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_6, %trueResult_30]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %6 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %7 = constant %6 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = -1 : i32} : <>, <i32>
    %8 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %9 = trunci %8 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%9] %outputs_0 {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %10 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %11 = trunci %10 {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_8, %dataResult_9 = load[%11] %outputs {handshake.bb = 1 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %12 = subi %dataResult, %dataResult_9 {handshake.bb = 1 : ui32, handshake.name = "subi0"} : <i32>
    %13 = cmpi sgt, %12, %7 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_10, %falseResult_11 = cond_br %13, %5 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %13, %3 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %13, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %13, %12 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %13, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %14 = merge %trueResult_10 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %15 = merge %trueResult_12 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %16 = merge %trueResult_14 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <i32>
    %17 = merge %trueResult_16 {handshake.bb = 2 : ui32, handshake.name = "merge3"} : <i32>
    %result_20, %index_21 = control_merge [%trueResult_18]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %18 = divsi %16, %17 {handshake.bb = 2 : ui32, handshake.name = "divsi0"} : <i32>
    %19 = br %18 {handshake.bb = 2 : ui32, handshake.name = "br1"} : <i32>
    %20 = br %14 {handshake.bb = 2 : ui32, handshake.name = "br2"} : <i32>
    %21 = br %15 {handshake.bb = 2 : ui32, handshake.name = "br3"} : <i32>
    %22 = br %result_20 {handshake.bb = 2 : ui32, handshake.name = "br4"} : <>
    %23 = mux %index_23 [%falseResult_15, %19] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %24 = mux %index_23 [%falseResult_11, %20] {handshake.bb = 3 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %25 = mux %index_23 [%falseResult_13, %21] {handshake.bb = 3 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %result_22, %index_23 = control_merge [%falseResult_19, %22]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %26 = source {handshake.bb = 3 : ui32, handshake.name = "source1"} : <>
    %27 = constant %26 {handshake.bb = 3 : ui32, handshake.name = "constant5", value = 1 : i32} : <>, <i32>
    %28 = addi %25, %27 {handshake.bb = 3 : ui32, handshake.name = "addi0"} : <i32>
    %29 = cmpi slt, %28, %24 {handshake.bb = 3 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_24, %falseResult_25 = cond_br %29, %28 {handshake.bb = 3 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_26, %falseResult_27 = cond_br %29, %23 {handshake.bb = 3 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_28, %falseResult_29 = cond_br %29, %24 {handshake.bb = 3 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_30, %falseResult_31 = cond_br %29, %result_22 {handshake.bb = 3 : ui32, handshake.name = "cond_br15"} : <i1>, <>
    %30 = mux %index_33 [%falseResult_3, %falseResult_27] {handshake.bb = 4 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %result_32, %index_33 = control_merge [%falseResult_7, %falseResult_31]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %30, %memEnd_1, %memEnd, %arg5 : <i32>, <>, <>, <>
  }
}

