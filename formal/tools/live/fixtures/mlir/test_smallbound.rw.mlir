module {
  handshake.func @test_smallbound(%arg0: memref<4xi32>, %arg1: memref<2xi32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["x", "y", "x_start", "y_start", "start"], resNames = ["x_end", "y_end", "end"]} {
    %0:3 = fork [3] %arg4 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %outputs, %memEnd = mem_controller[%arg1 : memref<2xi32>] %arg3 (%addressResult) %53#1 {connectedBlocks = [2 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i1>) -> !handshake.channel<i32>
    %1:2 = lsq[%arg0 : memref<4xi32>] (%arg2, %26#1, %addressResult_2, %addressResult_4, %dataResult_5, %53#0)  {groupSizes = [2 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i2>, !handshake.channel<i2>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %2 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %3 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i1>
    %4 = br %0#2 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %5 = mux %index [%3, %trueResult_16] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i1>, <i1>] to <i1>
    %6:3 = fork [3] %5 {handshake.bb = 1 : ui32, handshake.name = "fork1"} : <i1>
    %result, %index = control_merge [%4, %trueResult_18]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %7:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork2"} : <>
    %8 = constant %7#0 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = false} : <>, <i1>
    %9 = br %8 {handshake.bb = 1 : ui32, handshake.name = "br4"} : <i1>
    %10 = br %6#2 {handshake.bb = 1 : ui32, handshake.name = "br5"} : <i1>
    %11 = br %6#0 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i1>
    %12 = br %6#1 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i1>
    %13 = br %7#1 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <>
    %14 = mux %25#3 [%9, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i1>, <i1>] to <i1>
    %15:2 = fork [2] %14 {handshake.bb = 2 : ui32, handshake.name = "fork3"} : <i1>
    %16 = extui %15#0 {handshake.bb = 2 : ui32, handshake.name = "extui3"} : <i1> to <i2>
    %17 = extui %15#1 {handshake.bb = 2 : ui32, handshake.name = "extui4"} : <i1> to <i2>
    %18 = constant %28 {handshake.bb = 2 : ui32, handshake.name = "constant3", value = 1 : i2} : <>, <i2>
    %19 = mux %25#2 [%10, %trueResult_6] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i1>, <i1>] to <i1>
    %20 = mux %25#0 [%11, %trueResult_8] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i1>, <i1>] to <i1>
    %21:2 = fork [2] %20 {handshake.bb = 2 : ui32, handshake.name = "fork4"} : <i1>
    %22 = mux %25#1 [%12, %trueResult_10] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i1>, <i1>] to <i1>
    %23:2 = fork [2] %22 {handshake.bb = 2 : ui32, handshake.name = "fork5"} : <i1>
    %24 = extui %23#1 {handshake.bb = 2 : ui32, handshake.name = "extui5"} : <i1> to <i64>
    %result_0, %index_1 = control_merge [%13, %trueResult_12]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %25:4 = fork [4] %index_1 {handshake.bb = 2 : ui32, handshake.name = "fork6"} : <i1>
    %26:3 = fork [3] %result_0 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <>
    %27 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %28 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %29 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %30 = constant %29 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 1 : i64} : <>, <i64>
    %addressResult, %dataResult = load[%21#0] %outputs {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : <i1>, <i32>, <i1>, <i32>
    %31 = constant %26#0 {handshake.bb = 2 : ui32, handshake.name = "constant4", value = 0 : i2} : <>, <i2>
    %addressResult_2, %dataResult_3 = load[%31] %1#0 {handshake.bb = 2 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load1"} : <i2>, <i32>, <i2>, <i32>
    %32 = addi %dataResult, %dataResult_3 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i32>
    %33 = shli %24, %30 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %34 = trunci %33 {handshake.bb = 2 : ui32, handshake.name = "trunci0"} : <i64> to <i2>
    %35 = addi %34, %16 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i2>
    %addressResult_4, %dataResult_5 = store[%35] %32 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store2"} : <i2>, <i32>, <i2>, <i32>
    %36 = addi %17, %18 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i2>
    %37:2 = fork [2] %36 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i2>
    %38 = trunci %37#0 {handshake.bb = 2 : ui32, handshake.name = "trunci1"} : <i2> to <i1>
    %39 = constant %27 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = -2 : i2} : <>, <i2>
    %40 = cmpi ult, %37#1, %39 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i2>
    %41:5 = fork [5] %40 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <i1>
    %trueResult, %falseResult = cond_br %41#0, %38 {handshake.bb = 2 : ui32, handshake.name = "cond_br2"} : <i1>, <i1>
    sink %falseResult {handshake.name = "sink0"} : <i1>
    %trueResult_6, %falseResult_7 = cond_br %41#3, %19 {handshake.bb = 2 : ui32, handshake.name = "cond_br3"} : <i1>, <i1>
    %trueResult_8, %falseResult_9 = cond_br %41#1, %21#1 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <i1>
    sink %falseResult_9 {handshake.name = "sink1"} : <i1>
    %trueResult_10, %falseResult_11 = cond_br %41#2, %23#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i1>
    sink %falseResult_11 {handshake.name = "sink2"} : <i1>
    %trueResult_12, %falseResult_13 = cond_br %41#4, %26#2 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %42 = merge %falseResult_7 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i1>
    %43 = extui %42 {handshake.bb = 3 : ui32, handshake.name = "extui6"} : <i1> to <i2>
    %44 = constant %46 {handshake.bb = 3 : ui32, handshake.name = "constant13", value = 1 : i2} : <>, <i2>
    %result_14, %index_15 = control_merge [%falseResult_13]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    sink %index_15 {handshake.name = "sink3"} : <i1>
    %45 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %46 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %47 = addi %43, %44 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i2>
    %48:2 = fork [2] %47 {handshake.bb = 3 : ui32, handshake.name = "fork10"} : <i2>
    %49 = trunci %48#0 {handshake.bb = 3 : ui32, handshake.name = "trunci2"} : <i2> to <i1>
    %50 = constant %45 {handshake.bb = 3 : ui32, handshake.name = "constant14", value = -2 : i2} : <>, <i2>
    %51 = cmpi ult, %48#1, %50 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i2>
    %52:2 = fork [2] %51 {handshake.bb = 3 : ui32, handshake.name = "fork11"} : <i1>
    %trueResult_16, %falseResult_17 = cond_br %52#0, %49 {handshake.bb = 3 : ui32, handshake.name = "cond_br7"} : <i1>, <i1>
    sink %falseResult_17 {handshake.name = "sink4"} : <i1>
    %trueResult_18, %falseResult_19 = cond_br %52#1, %result_14 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %result_20, %index_21 = control_merge [%falseResult_19]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    sink %index_21 {handshake.name = "sink5"} : <i1>
    %53:2 = fork [2] %result_20 {handshake.bb = 4 : ui32, handshake.name = "fork12"} : <>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %1#1, %memEnd, %0#1 : <>, <>, <>
  }
}

