module {
  handshake.func @while_loop_1(%arg0: memref<1000xi32>, %arg1: memref<1000xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "a_start", "b_start", "start"], resNames = ["a_end", "b_end", "end"]} {
    %0:3 = fork [3] %arg4 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg1 : memref<1000xi32>] %arg3 (%addressResult_0) %21#1 {connectedBlocks = [1 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i10>) -> !handshake.channel<i32>
    %1:2 = lsq[%arg0 : memref<1000xi32>] (%arg2, %11#0, %addressResult, %addressResult_2, %dataResult_3, %21#0)  {groupSizes = [2 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i10>, !handshake.channel<i10>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %2 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %3 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i1>
    %4 = extui %3 {handshake.bb = 0 : ui32, handshake.name = "extui3"} : <i1> to <i32>
    %5 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %6 = mux %index [%4, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %7:4 = fork [4] %6 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i32>
    %8 = trunci %7#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i10>
    %9 = trunci %7#1 {handshake.bb = 1 : ui32, handshake.name = "trunci1"} : <i32> to <i10>
    %10 = trunci %7#2 {handshake.bb = 1 : ui32, handshake.name = "trunci2"} : <i32> to <i10>
    %result, %index = control_merge [%5, %trueResult_4]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %11:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <>
    %12 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %13 = constant %12 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 1000 : i32} : <>, <i32>
    %14 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %15 = constant %14 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%10] %1#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : false}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load0"} : <i10>, <i32>, <i10>, <i32>
    %addressResult_0, %dataResult_1 = load[%9] %outputs {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : <i10>, <i32>, <i10>, <i32>
    %16 = addi %dataResult, %dataResult_1 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %17:2 = fork [2] %16 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %addressResult_2, %dataResult_3 = store[%8] %17#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store2"} : <i10>, <i32>, <i10>, <i32>
    %18 = addi %7#3, %15 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %19 = cmpi slt, %17#1, %13 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %20:2 = fork [2] %19 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %trueResult, %falseResult = cond_br %20#1, %18 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i32>
    sink %falseResult {handshake.name = "sink0"} : <i32>
    %trueResult_4, %falseResult_5 = cond_br %20#0, %11#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <>
    %result_6, %index_7 = control_merge [%falseResult_5]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_7 {handshake.name = "sink1"} : <i1>
    %21:2 = fork [2] %result_6 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %1#1, %memEnd, %0#1 : <>, <>, <>
  }
}

