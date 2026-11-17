module {
  handshake.func @test_memory_14(%arg0: memref<4xi32>, %arg1: memref<4xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "a_start", "b_start", "start"], resNames = ["a_end", "b_end", "end"]} {
    %0:3 = fork [3] %arg4 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = lsq[%arg1 : memref<4xi32>] (%arg3, %9#0, %addressResult_0, %17#0, %addressResult_8, %dataResult_9, %40#1)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq2"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i2>, !handshake.control<>, !handshake.channel<i2>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %2:2 = lsq[%arg0 : memref<4xi32>] (%arg2, %9#2, %addressResult, %31#0, %addressResult_12, %dataResult_13, %40#0)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq3"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i2>, !handshake.control<>, !handshake.channel<i2>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
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
    %trueResult_2, %falseResult_3 = cond_br %13#2, %dataResult {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %13#1, %9#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <>
    %14 = merge %trueResult {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i2>
    %15:2 = fork [2] %14 {handshake.bb = 2 : ui32, handshake.name = "fork3"} : <i2>
    %16 = merge %trueResult_2 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %result_6, %index_7 = control_merge [%trueResult_4]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_7 {handshake.name = "sink0"} : <i1>
    %17:3 = lazy_fork [3] %result_6 {handshake.bb = 2 : ui32, handshake.name = "lazy_fork1"} : <>
    %18 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %19 = constant %18 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = 1 : i32} : <>, <i32>
    %20 = constant %17#2 {handshake.bb = 2 : ui32, handshake.name = "constant6", value = 0 : i32} : <>, <i32>
    %21 = addi %16, %19 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i32>
    %addressResult_8, %dataResult_9 = store[%15#0] %20 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store2"} : <i2>, <i32>, <i2>, <i32>
    %22 = br %21 {handshake.bb = 2 : ui32, handshake.name = "br4"} : <i32>
    %23 = br %15#1 {handshake.bb = 2 : ui32, handshake.name = "br5"} : <i2>
    %24 = br %17#1 {handshake.bb = 2 : ui32, handshake.name = "br6"} : <>
    %25 = mux %30#1 [%falseResult_3, %22] {handshake.bb = 3 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %26 = mux %30#0 [%falseResult, %23] {handshake.bb = 3 : ui32, handshake.name = "mux2"} : <i1>, [<i2>, <i2>] to <i2>
    %27:2 = fork [2] %26 {handshake.bb = 3 : ui32, handshake.name = "fork4"} : <i2>
    %28 = extui %27#1 {handshake.bb = 3 : ui32, handshake.name = "extui5"} : <i2> to <i3>
    %29 = constant %33 {handshake.bb = 3 : ui32, handshake.name = "constant2", value = 1 : i3} : <>, <i3>
    %result_10, %index_11 = control_merge [%falseResult_5, %24]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %30:2 = fork [2] %index_11 {handshake.bb = 3 : ui32, handshake.name = "fork5"} : <i1>
    %31:2 = lazy_fork [2] %result_10 {handshake.bb = 3 : ui32, handshake.name = "lazy_fork2"} : <>
    %32 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %33 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %addressResult_12, %dataResult_13 = store[%27#0] %25 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store3"} : <i2>, <i32>, <i2>, <i32>
    %34 = addi %28, %29 {handshake.bb = 3 : ui32, handshake.name = "addi1"} : <i3>
    %35:2 = fork [2] %34 {handshake.bb = 3 : ui32, handshake.name = "fork6"} : <i3>
    %36 = trunci %35#0 {handshake.bb = 3 : ui32, handshake.name = "trunci0"} : <i3> to <i2>
    %37 = constant %32 {handshake.bb = 3 : ui32, handshake.name = "constant3", value = -4 : i3} : <>, <i3>
    %38 = cmpi ult, %35#1, %37 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i3>
    %39:2 = fork [2] %38 {handshake.bb = 3 : ui32, handshake.name = "fork7"} : <i1>
    %trueResult_14, %falseResult_15 = cond_br %39#0, %36 {handshake.bb = 3 : ui32, handshake.name = "cond_br5"} : <i1>, <i2>
    sink %falseResult_15 {handshake.name = "sink1"} : <i2>
    %trueResult_16, %falseResult_17 = cond_br %39#1, %31#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %result_18, %index_19 = control_merge [%falseResult_17]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_19 {handshake.name = "sink2"} : <i1>
    %40:2 = fork [2] %result_18 {handshake.bb = 4 : ui32, handshake.name = "fork8"} : <>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %2#1, %1#1, %0#1 : <>, <>, <>
  }
}

