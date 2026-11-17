module {
  handshake.func @divergent_paths(%arg0: memref<100xi32>, %arg1: memref<100xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "a_start", "b_start", "start"], resNames = ["a_end", "b_end", "end"]} {
    %0:3 = fork [3] %arg4 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %memEnd = mem_controller[%arg1 : memref<100xi32>] %arg3 (%11, %addressResult_2, %dataResult_3) %31#1 {connectedBlocks = [1 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>, !handshake.channel<i7>, !handshake.channel<i32>) -> ()
    %1:2 = lsq[%arg0 : memref<100xi32>] (%arg2, %10#0, %addressResult, %addressResult_0, %dataResult_1, %31#0)  {groupSizes = [2 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i7>, !handshake.channel<i7>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %2 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %3 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i1>
    %4 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i1> to <i7>
    %5 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %6 = mux %index [%4, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i7>, <i7>] to <i7>
    %7:4 = fork [4] %6 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i7>
    %8 = extui %7#3 {handshake.bb = 1 : ui32, handshake.name = "extui4"} : <i7> to <i8>
    %9 = constant %14#0 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 1 : i8} : <>, <i8>
    %result, %index = control_merge [%5, %trueResult_4]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %10:3 = fork [3] %result {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <>
    %11 = constant %10#1 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %12 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %13 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %14:2 = fork [2] %13 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <>
    %15 = constant %14#1 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 1 : i32} : <>, <i32>
    %16 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %17 = constant %16 {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 2 : i32} : <>, <i32>
    %18 = source {handshake.bb = 1 : ui32, handshake.name = "source3"} : <>
    %19 = constant %18 {handshake.bb = 1 : ui32, handshake.name = "constant9", value = 255 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%7#2] %1#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : false}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load0"} : <i7>, <i32>, <i7>, <i32>
    %20 = xori %dataResult, %19 {handshake.bb = 1 : ui32, handshake.name = "xori0"} : <i32>
    %21:3 = fork [3] %20 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %22 = addi %21#2, %17 {dynamatic.predict = {location = "end", marker = 3 : i32, type = "", values = ""}, dynamatic.predict.result_idx = 0 : i32, handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %23 = shli %21#1, %15 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i32>
    %24 = addi %21#0, %23 {dynamatic.predict = {location = "end", marker = 3 : i32, type = "", values = ""}, dynamatic.predict.result_idx = 0 : i32, handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %addressResult_0, %dataResult_1 = store[%7#1] %22 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store1"} : <i7>, <i32>, <i7>, <i32>
    %addressResult_2, %dataResult_3 = store[%7#0] %24 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store2"} : <i7>, <i32>, <i7>, <i32>
    %25 = addi %8, %9 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i8>
    %26:2 = fork [2] %25 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i8>
    %27 = trunci %26#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i8> to <i7>
    %28 = constant %12 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 100 : i8} : <>, <i8>
    %29 = cmpi ult, %26#1, %28 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i8>
    %30:2 = fork [2] %29 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i1>
    %trueResult, %falseResult = cond_br %30#0, %27 {handshake.bb = 1 : ui32, handshake.name = "cond_br1"} : <i1>, <i7>
    sink %falseResult {handshake.name = "sink0"} : <i7>
    %trueResult_4, %falseResult_5 = cond_br %30#1, %10#2 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <>
    %result_6, %index_7 = control_merge [%falseResult_5]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_7 {handshake.name = "sink1"} : <i1>
    %31:2 = fork [2] %result_6 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %1#1, %memEnd, %0#1 : <>, <>, <>
  }
}

