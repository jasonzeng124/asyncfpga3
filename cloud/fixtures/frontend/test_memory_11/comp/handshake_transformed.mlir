module {
  handshake.func @test_memory_11(%arg0: memref<4xi32>, %arg1: !handshake.control<>, %arg2: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "a_start", "start"], resNames = ["a_end", "end"]} {
    %0:3 = fork [3] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:4 = lsq[%arg0 : memref<4xi32>] (%arg1, %10#0, %addressResult, %addressResult_0, %addressResult_2, %dataResult_3, %29#0, %addressResult_10, %addressResult_12, %dataResult_13, %result_18)  {groupSizes = [3 : i32, 2 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i2>, !handshake.channel<i2>, !handshake.channel<i2>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i2>, !handshake.channel<i2>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>)
    %2 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = true} : <>, <i1>
    %3 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br1"} : <i1>
    %4 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui5"} : <i1> to <i2>
    %5 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <>
    %6 = mux %index [%4, %trueResult] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i2>, <i2>] to <i2>
    %7:4 = fork [4] %6 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i2>
    %8 = extui %7#3 {handshake.bb = 1 : ui32, handshake.name = "extui6"} : <i2> to <i3>
    %9 = constant %11#0 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 1 : i3} : <>, <i3>
    %result, %index = control_merge [%5, %trueResult_4]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %10:3 = lazy_fork [3] %result {handshake.bb = 1 : ui32, handshake.name = "lazy_fork0"} : <>
    %11:2 = fork [2] %10#2 {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <>
    %12 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %13 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %14 = constant %13 {handshake.bb = 1 : ui32, handshake.name = "constant9", value = -1 : i2} : <>, <i2>
    %15 = addi %7#0, %14 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i2>
    %addressResult, %dataResult = load[%15] %1#0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load0"} : <i2>, <i32>, <i2>, <i32>
    %addressResult_0, %dataResult_1 = load[%7#2] %1#1 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load1"} : <i2>, <i32>, <i2>, <i32>
    %16 = addi %dataResult, %dataResult_1 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %addressResult_2, %dataResult_3 = store[%7#1] %16 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store2"} : <i2>, <i32>, <i2>, <i32>
    %17 = addi %8, %9 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i3>
    %18:2 = fork [2] %17 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i3>
    %19 = trunci %18#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i3> to <i2>
    %20 = constant %12 {handshake.bb = 1 : ui32, handshake.name = "constant10", value = -4 : i3} : <>, <i3>
    %21 = cmpi ult, %18#1, %20 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i3>
    %22:3 = fork [3] %21 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %trueResult, %falseResult = cond_br %22#0, %19 {handshake.bb = 1 : ui32, handshake.name = "cond_br2"} : <i1>, <i2>
    sink %falseResult {handshake.name = "sink0"} : <i2>
    %trueResult_4, %falseResult_5 = cond_br %22#1, %10#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br3"} : <i1>, <>
    %23 = constant %11#1 {handshake.bb = 1 : ui32, handshake.name = "constant11", value = true} : <>, <i1>
    %trueResult_6, %falseResult_7 = cond_br %22#2, %23 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i1>
    sink %trueResult_6 {handshake.name = "sink1"} : <i1>
    %24 = extui %falseResult_7 {handshake.bb = 2 : ui32, handshake.name = "extui7"} : <i1> to <i2>
    %25 = mux %index_9 [%24, %trueResult_14] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i2>, <i2>] to <i2>
    %26:3 = fork [3] %25 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i2>
    %27 = extui %26#2 {handshake.bb = 2 : ui32, handshake.name = "extui8"} : <i2> to <i3>
    %28 = constant %32 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 1 : i3} : <>, <i3>
    %result_8, %index_9 = control_merge [%falseResult_5, %trueResult_16]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %29:2 = fork [2] %result_8 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <>
    %30 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %31 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %32 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %33 = constant %31 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = -1 : i2} : <>, <i2>
    %34 = addi %26#0, %33 {handshake.bb = 2 : ui32, handshake.name = "addi3"} : <i2>
    %addressResult_10, %dataResult_11 = load[%34] %1#2 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load3"} : <i2>, <i32>, <i2>, <i32>
    %addressResult_12, %dataResult_13 = store[%26#1] %dataResult_11 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store4"} : <i2>, <i32>, <i2>, <i32>
    %35 = addi %27, %28 {handshake.bb = 2 : ui32, handshake.name = "addi4"} : <i3>
    %36:2 = fork [2] %35 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i3>
    %37 = trunci %36#0 {handshake.bb = 2 : ui32, handshake.name = "trunci1"} : <i3> to <i2>
    %38 = constant %30 {handshake.bb = 2 : ui32, handshake.name = "constant14", value = -4 : i3} : <>, <i3>
    %39 = cmpi ult, %36#1, %38 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i3>
    %40:2 = fork [2] %39 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i1>
    %trueResult_14, %falseResult_15 = cond_br %40#0, %37 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i2>
    sink %falseResult_15 {handshake.name = "sink2"} : <i2>
    %trueResult_16, %falseResult_17 = cond_br %40#1, %29#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %result_18, %index_19 = control_merge [%falseResult_17]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_19 {handshake.name = "sink3"} : <i1>
    end {handshake.bb = 3 : ui32, handshake.name = "end0"} %1#3, %0#1 : <>, <>
  }
}

