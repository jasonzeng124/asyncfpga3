module {
  handshake.func @test_memory_13(%arg0: memref<4xi32>, %arg1: memref<4xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "a_start", "b_start", "start"], resNames = ["a_end", "b_end", "end"]} {
    %0:3 = fork [3] %arg4 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = lsq[%arg1 : memref<4xi32>] (%arg3, %9#0, %addressResult_0, %16#0, %addressResult_8, %dataResult_9, %39#1)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq2"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i2>, !handshake.control<>, !handshake.channel<i2>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %2:2 = lsq[%arg0 : memref<4xi32>] (%arg2, %9#2, %addressResult, %30#0, %addressResult_12, %dataResult_13, %39#0)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq3"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i2>, !handshake.control<>, !handshake.channel<i2>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %3 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %4 = br %3 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i1>
    %5 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui4"} : <i1> to <i2>
    %6 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %7 = mux %index [%5, %trueResult_14] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i2>, <i2>] to <i2>
    %8:3 = fork [3] %7 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i2>
    %result, %index = control_merge [%6, %trueResult_16]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %9:3 = lazy_fork [3] %result {handshake.bb = 1 : ui32, handshake.name = "lazy_fork0"} : <>
    %10 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %11 = constant %10 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 5 : i32} : <>, <i32>
    %addressResult, %dataResult = load[%8#1] %2#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load0"} : <i2>, <i32>, <i2>, <i32>
    %addressResult_0, %dataResult_1 = load[%8#0] %1#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load1"} : <i2>, <i32>, <i2>, <i32>
    %12 = cmpi sgt, %dataResult_1, %11 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %13:3 = fork [3] %12 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <i1>
    %trueResult, %falseResult = cond_br %13#0, %8#2 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i2>
    %trueResult_2, %falseResult_3 = cond_br %13#2, %9#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %trueResult_4, %falseResult_5 = cond_br %13#1, %dataResult {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    sink %trueResult_4 {handshake.name = "sink0"} : <i32>
    %14 = merge %trueResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i2>
    %15:2 = fork [2] %14 {handshake.bb = 2 : ui32, handshake.name = "fork3"} : <i2>
    %result_6, %index_7 = control_merge [%trueResult_2]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_7 {handshake.name = "sink1"} : <i1>
    %16:3 = lazy_fork [3] %result_6 {handshake.bb = 2 : ui32, handshake.name = "lazy_fork1"} : <>
    %17:2 = fork [2] %16#2 {handshake.bb = 2 : ui32, handshake.name = "fork4"} : <>
    %18 = constant %17#1 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = 0 : i32} : <>, <i32>
    %addressResult_8, %dataResult_9 = store[%15#0] %18 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store2"} : <i2>, <i32>, <i2>, <i32>
    %19 = constant %17#0 {handshake.bb = 2 : ui32, handshake.name = "constant2", value = false} : <>, <i1>
    %20 = br %19 {handshake.bb = 2 : ui32, handshake.name = "br4"} : <i1>
    %21 = extui %20 {handshake.bb = 2 : ui32, handshake.name = "extui5"} : <i1> to <i32>
    %22 = br %15#1 {handshake.bb = 2 : ui32, handshake.name = "br5"} : <i2>
    %23 = br %16#1 {handshake.bb = 2 : ui32, handshake.name = "br6"} : <>
    %24 = mux %29#1 [%falseResult_5, %21] {handshake.bb = 3 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %25 = mux %29#0 [%falseResult, %22] {handshake.bb = 3 : ui32, handshake.name = "mux2"} : <i1>, [<i2>, <i2>] to <i2>
    %26:2 = fork [2] %25 {handshake.bb = 3 : ui32, handshake.name = "fork5"} : <i2>
    %27 = extui %26#1 {handshake.bb = 3 : ui32, handshake.name = "extui6"} : <i2> to <i3>
    %28 = constant %32 {handshake.bb = 3 : ui32, handshake.name = "constant3", value = 1 : i3} : <>, <i3>
    %result_10, %index_11 = control_merge [%falseResult_3, %23]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %29:2 = fork [2] %index_11 {handshake.bb = 3 : ui32, handshake.name = "fork6"} : <i1>
    %30:2 = lazy_fork [2] %result_10 {handshake.bb = 3 : ui32, handshake.name = "lazy_fork2"} : <>
    %31 = source {handshake.bb = 3 : ui32, handshake.name = "source1"} : <>
    %32 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %addressResult_12, %dataResult_13 = store[%26#0] %24 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store3"} : <i2>, <i32>, <i2>, <i32>
    %33 = addi %27, %28 {handshake.bb = 3 : ui32, handshake.name = "addi0"} : <i3>
    %34:2 = fork [2] %33 {handshake.bb = 3 : ui32, handshake.name = "fork7"} : <i3>
    %35 = trunci %34#0 {handshake.bb = 3 : ui32, handshake.name = "trunci0"} : <i3> to <i2>
    %36 = constant %31 {handshake.bb = 3 : ui32, handshake.name = "constant8", value = -4 : i3} : <>, <i3>
    %37 = cmpi ult, %34#1, %36 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i3>
    %38:2 = fork [2] %37 {handshake.bb = 3 : ui32, handshake.name = "fork8"} : <i1>
    %trueResult_14, %falseResult_15 = cond_br %38#0, %35 {handshake.bb = 3 : ui32, handshake.name = "cond_br5"} : <i1>, <i2>
    sink %falseResult_15 {handshake.name = "sink2"} : <i2>
    %trueResult_16, %falseResult_17 = cond_br %38#1, %30#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %result_18, %index_19 = control_merge [%falseResult_17]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_19 {handshake.name = "sink3"} : <i1>
    %39:2 = fork [2] %result_18 {handshake.bb = 4 : ui32, handshake.name = "fork9"} : <>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %2#1, %1#1, %0#1 : <>, <>, <>
  }
}

