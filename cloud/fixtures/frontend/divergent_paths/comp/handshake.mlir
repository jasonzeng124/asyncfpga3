module {
  handshake.func @divergent_paths(%arg0: memref<100xi32>, %arg1: memref<100xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "a_start", "b_start", "start"], resNames = ["a_end", "b_end", "end"]} {
    %memEnd = mem_controller[%arg1 : memref<100xi32>] %arg3 (%4, %addressResult_2, %dataResult_3) %result_6 {connectedBlocks = [1 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> ()
    %0:2 = lsq[%arg0 : memref<100xi32>] (%arg2, %result, %addressResult, %addressResult_0, %dataResult_1, %result_6)  {groupSizes = [2 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %1 = constant %arg4 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i32>
    %3 = br %arg4 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %4 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %5 = mux %index [%2, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%3, %trueResult_4]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %6 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %7 = constant %6 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 100 : i32} : <>, <i32>
    %8 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %9 = constant %8 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 1 : i32} : <>, <i32>
    %10 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %11 = constant %10 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 2 : i32} : <>, <i32>
    %12 = source {handshake.bb = 1 : ui32, handshake.name = "source3"} : <>
    %13 = constant %12 {handshake.bb = 1 : ui32, handshake.name = "constant9", value = 255 : i32} : <>, <i32>
    %14 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %15 = trunci %14 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%15] %0#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %16 = xori %dataResult, %13 {handshake.bb = 1 : ui32, handshake.name = "xori0"} : <i32>
    %17 = addi %16, %11 {dynamatic.predict = {location = "end", marker = 3 : i32, type = "", values = ""}, dynamatic.predict.result_idx = 0 : i32, handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %18 = shli %16, %9 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %19 = addi %16, %18 {dynamatic.predict = {location = "end", marker = 3 : i32, type = "", values = ""}, dynamatic.predict.result_idx = 0 : i32, handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %20 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %21 = trunci %20 {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_0, %dataResult_1 = store[%21] %17 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : <i32>, <i32>, <i32>, <i32>
    %22 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %23 = trunci %22 {handshake.bb = 1 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_2, %dataResult_3 = store[%23] %19 {handshake.bb = 1 : ui32, handshake.name = "store2"} : <i32>, <i32>, <i32>, <i32>
    %24 = addi %5, %9 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %25 = cmpi ult, %24, %7 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %25, %24 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %25, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <>
    %result_6, %index_7 = control_merge [%falseResult_5]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %0#1, %memEnd, %arg4 : <>, <>, <>
  }
}

