module {
  handshake.func @gather(%arg0: memref<32xi32>, %arg1: memref<32xi32>, %arg2: !handshake.channel<i32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "n", "a_start", "b_start", "start"], resNames = ["out0", "a_end", "b_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg1 : memref<32xi32>] %arg4 (%addressResult) %result_16 {connectedBlocks = [1 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_0, %memEnd_1 = mem_controller[%arg0 : memref<32xi32>] %arg3 (%addressResult_6) %result_16 {connectedBlocks = [1 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %0 = constant %arg5 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = cmpi sgt, %arg2, %0 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %1, %0 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %1, %arg2 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %1, %arg5 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %2 = mux %index [%trueResult, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %3 = mux %index [%trueResult, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %4 = mux %index [%trueResult_2, %trueResult_12] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_4, %trueResult_14]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %5 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %6 = constant %5 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 32 : i32} : <>, <i32>
    %7 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %8 = constant %7 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %9 = extui %2 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %10 = trunci %9 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%10] %outputs {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %11 = trunci %dataResult {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i32> to <i32>
    %addressResult_6, %dataResult_7 = load[%11] %outputs_0 {handshake.bb = 1 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %12 = addi %2, %8 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %13 = muli %dataResult_7, %12 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %14 = addi %3, %13 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %15 = addi %2, %8 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %16 = cmpi slt, %15, %4 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %17 = cmpi ult, %15, %6 {handshake.bb = 1 : ui32, handshake.name = "cmpi2"} : <i32>
    %18 = andi %16, %17 {handshake.bb = 1 : ui32, handshake.name = "andi0"} : <i1>
    %trueResult_8, %falseResult_9 = cond_br %18, %15 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %18, %14 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %18, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %18, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %19 = mux %index_17 [%falseResult, %falseResult_11] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_16, %index_17 = control_merge [%falseResult_5, %falseResult_15]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %19, %memEnd_1, %memEnd, %arg5 : <i32>, <>, <>, <>
  }
}

