module {
  handshake.func @test_unroll(%arg0: memref<20xi32>, %arg1: memref<20xi32>, %arg2: memref<20xi32>, %arg3: memref<20xi32>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, %arg8: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["A", "B", "C", "result", "A_start", "B_start", "C_start", "result_start", "start"], resNames = ["A_end", "B_end", "C_end", "result_end", "end"]} {
    %0:2 = lsq[%2 : memref<20xi32>] (%arg8, %result, %addressResult_7, %dataResult_8, %result_13, %addressResult_15, %result_25)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %memEnd = mem_controller[%arg3 : memref<20xi32>] %arg7 (%20, %addressResult_19, %dataResult_20) %result_25 {connectedBlocks = [2 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> ()
    %outputs, %memEnd_0 = mem_controller[%arg2 : memref<20xi32>] %arg6 (%addressResult_17) %result_25 {connectedBlocks = [2 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_1, %memEnd_2 = mem_controller[%arg1 : memref<20xi32>] %arg5 (%addressResult_5) %result_25 {connectedBlocks = [1 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_3, %memEnd_4 = mem_controller[%arg0 : memref<20xi32>] %arg4 (%addressResult) %result_25 {connectedBlocks = [1 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %1 = constant %arg8 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 0 : i32} : <>, <i32>
    %2 = "handshake.ram"() {handshake.name = "ram0", initialValue = dense<0> : memref<20xi32>} : () -> memref<20xi32>
    %3 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i32>
    %4 = br %arg8 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %5 = mux %index [%3, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%4, %trueResult_9]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %6 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %7 = constant %6 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 20 : i32} : <>, <i32>
    %8 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 0 : i32} : <>, <i32>
    %9 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %10 = constant %9 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 1 : i32} : <>, <i32>
    %11 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %12 = trunci %11 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%12] %outputs_3 {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %13 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %14 = trunci %13 {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_5, %dataResult_6 = load[%14] %outputs_1 {handshake.bb = 1 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %15 = muli %dataResult, %dataResult_6 {handshake.bb = 1 : ui32, handshake.name = "muli0"} : <i32>
    %16 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %17 = trunci %16 {handshake.bb = 1 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_7, %dataResult_8 = store[%17] %15 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : <i32>, <i32>, <i32>, <i32>
    %18 = addi %5, %10 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %19 = cmpi ult, %18, %7 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %19, %18 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_9, %falseResult_10 = cond_br %19, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %trueResult_11, %falseResult_12 = cond_br %19, %8 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %20 = constant %result_13 {handshake.bb = 2 : ui32, handshake.name = "constant0", value = 1 : i32} : <>, <i32>
    %21 = mux %index_14 [%falseResult_12, %trueResult_21] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result_13, %index_14 = control_merge [%falseResult_10, %trueResult_23]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %22 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %23 = constant %22 {handshake.bb = 2 : ui32, handshake.name = "constant6", value = 20 : i32} : <>, <i32>
    %24 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %25 = constant %24 {handshake.bb = 2 : ui32, handshake.name = "constant7", value = 1 : i32} : <>, <i32>
    %26 = extui %21 {handshake.bb = 2 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %27 = trunci %26 {handshake.bb = 2 : ui32, handshake.name = "index_cast3"} : <i64> to <i32>
    %addressResult_15, %dataResult_16 = load[%27] %0#0 {handshake.bb = 2 : ui32, handshake.name = "load3"} : <i32>, <i32>, <i32>, <i32>
    %28 = extui %21 {handshake.bb = 2 : ui32, handshake.name = "extui4"} : <i32> to <i64>
    %29 = trunci %28 {handshake.bb = 2 : ui32, handshake.name = "index_cast4"} : <i64> to <i32>
    %addressResult_17, %dataResult_18 = load[%29] %outputs {handshake.bb = 2 : ui32, handshake.name = "load4"} : <i32>, <i32>, <i32>, <i32>
    %30 = muli %dataResult_16, %dataResult_18 {handshake.bb = 2 : ui32, handshake.name = "muli3"} : <i32>
    %31 = extui %21 {handshake.bb = 2 : ui32, handshake.name = "extui5"} : <i32> to <i64>
    %32 = trunci %31 {handshake.bb = 2 : ui32, handshake.name = "index_cast5"} : <i64> to <i32>
    %addressResult_19, %dataResult_20 = store[%32] %30 {handshake.bb = 2 : ui32, handshake.name = "store5"} : <i32>, <i32>, <i32>, <i32>
    %33 = addi %21, %25 {handshake.bb = 2 : ui32, handshake.name = "addi3"} : <i32>
    %34 = cmpi ult, %33, %23 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_21, %falseResult_22 = cond_br %34, %33 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_23, %falseResult_24 = cond_br %34, %result_13 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %result_25, %index_26 = control_merge [%falseResult_24]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    end {handshake.bb = 3 : ui32, handshake.name = "end0"} %memEnd_4, %memEnd_2, %memEnd_0, %memEnd, %arg8 : <>, <>, <>, <>, <>
  }
}

