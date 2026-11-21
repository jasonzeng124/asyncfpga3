module {
  handshake.func @test_memory_17(%arg0: memref<4xi32>, %arg1: memref<4xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "a_start", "b_start", "start"], resNames = ["a_end", "b_end", "end"]} {
    %0:3 = fork [3] %arg4 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = lsq[%arg1 : memref<4xi32>] (%arg3, %8#0, %addressResult, %16#0, %addressResult_6, %dataResult_7, %40#1)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i2>, !handshake.control<>, !handshake.channel<i2>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %memEnd = mem_controller[%arg0 : memref<4xi32>] %arg2 (%31, %addressResult_10, %dataResult_11) %40#0 {connectedBlocks = [3 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>, !handshake.channel<i2>, !handshake.channel<i32>) -> ()
    %2 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %3 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i1>
    %4 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i1> to <i2>
    %5 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %6 = mux %index [%4, %trueResult_12] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i2>, <i2>] to <i2>
    %7:2 = fork [2] %6 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i2>
    %result, %index = control_merge [%5, %trueResult_14]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %8:3 = lazy_fork [3] %result {handshake.bb = 1 : ui32, handshake.name = "lazy_fork0"} : <>
    %9 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %10 = constant %9 {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 5 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%7#0] %1#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load0"} : <i2>, <i32>, <i2>, <i32>
    %11 = cmpi sgt, %dataResult, %10 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %12:3 = fork [3] %11 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i1>
    %trueResult, %falseResult = cond_br %12#0, %7#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i2>
    %trueResult_0, %falseResult_1 = cond_br %12#2, %8#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %13 = constant %8#2 {handshake.bb = 1 : ui32, handshake.name = "constant9", value = true} : <>, <i1>
    %trueResult_2, %falseResult_3 = cond_br %12#1, %13 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i1>
    sink %trueResult_2 {handshake.name = "sink0"} : <i1>
    %14 = merge %trueResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i2>
    %15:2 = fork [2] %14 {handshake.bb = 2 : ui32, handshake.name = "fork3"} : <i2>
    %result_4, %index_5 = control_merge [%trueResult_0]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_5 {handshake.name = "sink1"} : <i1>
    %16:3 = lazy_fork [3] %result_4 {handshake.bb = 2 : ui32, handshake.name = "lazy_fork1"} : <>
    %17:2 = fork [2] %16#2 {handshake.bb = 2 : ui32, handshake.name = "fork4"} : <>
    %18 = constant %17#1 {handshake.bb = 2 : ui32, handshake.name = "constant6", value = 0 : i32} : <>, <i32>
    %addressResult_6, %dataResult_7 = store[%15#0] %18 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store1"} : <i2>, <i32>, <i2>, <i32>
    %19 = constant %17#0 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = false} : <>, <i1>
    %20 = br %19 {handshake.bb = 2 : ui32, handshake.name = "br4"} : <i1>
    %21 = br %15#1 {handshake.bb = 2 : ui32, handshake.name = "br5"} : <i2>
    %22 = br %16#1 {handshake.bb = 2 : ui32, handshake.name = "br6"} : <>
    %23 = mux %29#1 [%falseResult_3, %20] {handshake.bb = 3 : ui32, handshake.name = "mux1"} : <i1>, [<i1>, <i1>] to <i1>
    %24 = extui %23 {handshake.bb = 3 : ui32, handshake.name = "extui4"} : <i1> to <i32>
    %25 = mux %29#0 [%falseResult, %21] {handshake.bb = 3 : ui32, handshake.name = "mux2"} : <i1>, [<i2>, <i2>] to <i2>
    %26:2 = fork [2] %25 {handshake.bb = 3 : ui32, handshake.name = "fork5"} : <i2>
    %27 = extui %26#1 {handshake.bb = 3 : ui32, handshake.name = "extui5"} : <i2> to <i3>
    %28 = constant %33 {handshake.bb = 3 : ui32, handshake.name = "constant11", value = 1 : i3} : <>, <i3>
    %result_8, %index_9 = control_merge [%falseResult_1, %22]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %29:2 = fork [2] %index_9 {handshake.bb = 3 : ui32, handshake.name = "fork6"} : <i1>
    %30:2 = fork [2] %result_8 {handshake.bb = 3 : ui32, handshake.name = "fork7"} : <>
    %31 = constant %30#0 {handshake.bb = 3 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %32 = source {handshake.bb = 3 : ui32, handshake.name = "source1"} : <>
    %33 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %addressResult_10, %dataResult_11 = store[%26#0] %24 {handshake.bb = 3 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "store2"} : <i2>, <i32>, <i2>, <i32>
    %34 = addi %27, %28 {handshake.bb = 3 : ui32, handshake.name = "addi0"} : <i3>
    %35:2 = fork [2] %34 {handshake.bb = 3 : ui32, handshake.name = "fork8"} : <i3>
    %36 = trunci %35#0 {handshake.bb = 3 : ui32, handshake.name = "trunci0"} : <i3> to <i2>
    %37 = constant %32 {handshake.bb = 3 : ui32, handshake.name = "constant12", value = -4 : i3} : <>, <i3>
    %38 = cmpi ult, %35#1, %37 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i3>
    %39:2 = fork [2] %38 {handshake.bb = 3 : ui32, handshake.name = "fork9"} : <i1>
    %trueResult_12, %falseResult_13 = cond_br %39#0, %36 {handshake.bb = 3 : ui32, handshake.name = "cond_br5"} : <i1>, <i2>
    sink %falseResult_13 {handshake.name = "sink2"} : <i2>
    %trueResult_14, %falseResult_15 = cond_br %39#1, %30#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %result_16, %index_17 = control_merge [%falseResult_15]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_17 {handshake.name = "sink3"} : <i1>
    %40:2 = fork [2] %result_16 {handshake.bb = 4 : ui32, handshake.name = "fork10"} : <>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %memEnd, %1#1, %0#1 : <>, <>, <>
  }
}

