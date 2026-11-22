module {
  handshake.func @test_memory_2(%arg0: memref<5xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "n", "a_start", "start"], resNames = ["a_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg0 : memref<5xi32>] %arg2 (%5, %addressResult, %addressResult_4, %dataResult_5) %result_12 {connectedBlocks = [1 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> !handshake.channel<i32>
    %0 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %1 = constant %0 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = -1 : i32} : <>, <i32>
    %2 = constant %arg3 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 0 : i32} : <>, <i32>
    %3 = addi %arg1, %1 {handshake.bb = 0 : ui32, handshake.name = "addi0"} : <i32>
    %4 = cmpi sgt, %3, %2 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %4, %2 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %4, %3 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %4, %arg3 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %5 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %6 = mux %index [%trueResult, %trueResult_6] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %7 = mux %index [%trueResult_0, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_2, %trueResult_10]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %8 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %9 = constant %8 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 5 : i32} : <>, <i32>
    %10 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %11 = constant %10 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 1 : i32} : <>, <i32>
    %12 = addi %6, %11 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %13 = extui %12 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %14 = trunci %13 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%14] %outputs {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %15 = addi %dataResult, %9 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %16 = extui %6 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %17 = trunci %16 {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_4, %dataResult_5 = store[%17] %15 {handshake.bb = 1 : ui32, handshake.name = "store1"} : <i32>, <i32>, <i32>, <i32>
    %18 = addi %6, %11 {handshake.bb = 1 : ui32, handshake.name = "addi3"} : <i32>
    %19 = cmpi slt, %18, %7 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_6, %falseResult_7 = cond_br %19, %18 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %19, %7 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %19, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %result_12, %index_13 = control_merge [%falseResult_3, %falseResult_11]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %memEnd, %arg3 : <>, <>
  }
}

