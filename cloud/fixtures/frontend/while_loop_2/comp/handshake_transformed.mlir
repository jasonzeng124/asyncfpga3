module {
  handshake.func @while_loop_2(%arg0: memref<1000xi32>, %arg1: !handshake.control<>, %arg2: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "a_start", "start"], resNames = ["a_end", "end"]} {
    %0:3 = fork [3] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = lsq[%arg0 : memref<1000xi32>] (%arg1, %9#0, %addressResult, %18#1, %addressResult_6, %dataResult_7, %18#2)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i10>, !handshake.control<>, !handshake.channel<i10>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %2 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %3 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i1>
    %4 = extui %3 {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i1> to <i32>
    %5 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %6 = mux %index [%4, %falseResult_3] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %7:3 = fork [3] %6 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i32>
    %8 = trunci %7#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i10>
    %result, %index = control_merge [%5, %falseResult_1]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %9:2 = lazy_fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "lazy_fork0"} : <>
    %10 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %11 = constant %10 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 1 : i32} : <>, <i32>
    %12 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %13 = constant %12 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 0 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%8] %1#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load0"} : <i10>, <i32>, <i10>, <i32>
    %14 = cmpi eq, %dataResult, %13 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %15:3 = fork [3] %14 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i1>
    %16 = addi %7#2, %11 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %trueResult, %falseResult = cond_br %15#2, %7#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i32>
    sink %falseResult {handshake.name = "sink0"} : <i32>
    %trueResult_0, %falseResult_1 = cond_br %15#1, %9#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <>
    %trueResult_2, %falseResult_3 = cond_br %15#0, %16 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    sink %trueResult_2 {handshake.name = "sink1"} : <i32>
    %17 = merge %trueResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %result_4, %index_5 = control_merge [%trueResult_0]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_5 {handshake.name = "sink2"} : <i1>
    %18:3 = fork [3] %result_4 {handshake.bb = 2 : ui32, handshake.name = "fork3"} : <>
    %19 = constant %18#0 {handshake.bb = 2 : ui32, handshake.name = "constant2", value = 0 : i10} : <>, <i10>
    %addressResult_6, %dataResult_7 = store[%19] %17 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store1"} : <i10>, <i32>, <i10>, <i32>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %1#1, %0#1 : <>, <>
  }
}

