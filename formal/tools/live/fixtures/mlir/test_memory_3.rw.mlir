module {
  handshake.func @test_memory_3(%arg0: memref<4xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "n", "a_start", "start"], resNames = ["a_end", "end"]} {
    %0:4 = fork [4] %arg3 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg1 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2:2 = lsq[%arg0 : memref<4xi32>] (%arg2, %14#0, %addressResult, %21#0, %addressResult_12, %dataResult_13, %result_22)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i2>, !handshake.control<>, !handshake.channel<i2>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %3 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %4 = cmpi sgt, %1#1, %3 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %5:3 = fork [3] %4 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %6 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = false} : <>, <i1>
    %trueResult, %falseResult = cond_br %5#0, %6 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i1>
    sink %falseResult {handshake.name = "sink0"} : <i1>
    %7 = extui %trueResult {handshake.bb = 0 : ui32, handshake.name = "extui2"} : <i1> to <i32>
    %trueResult_0, %falseResult_1 = cond_br %5#2, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    sink %falseResult_1 {handshake.name = "sink1"} : <i32>
    %trueResult_2, %falseResult_3 = cond_br %5#1, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %8 = mux %13#0 [%7, %trueResult_16] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %9:2 = fork [2] %8 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %10 = trunci %9#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i2>
    %11 = mux %13#1 [%trueResult_0, %trueResult_18] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %12:2 = fork [2] %11 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %result, %index = control_merge [%trueResult_2, %trueResult_20]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %13:2 = fork [2] %index {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i1>
    %14:2 = lazy_fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "lazy_fork0"} : <>
    %addressResult, %dataResult = load[%10] %2#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load0"} : <i2>, <i32>, <i2>, <i32>
    %15 = cmpi eq, %dataResult, %12#1 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %16:3 = fork [3] %15 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i1>
    %trueResult_4, %falseResult_5 = cond_br %16#2, %12#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %16#1, %9#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %16#0, %14#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <>
    %17 = merge %trueResult_4 {handshake.bb = 2 : ui32, handshake.name = "merge0"} : <i32>
    %18 = merge %trueResult_6 {handshake.bb = 2 : ui32, handshake.name = "merge1"} : <i32>
    %19:2 = fork [2] %18 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i32>
    %20 = trunci %19#0 {handshake.bb = 2 : ui32, handshake.name = "trunci1"} : <i32> to <i2>
    %result_10, %index_11 = control_merge [%trueResult_8]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    sink %index_11 {handshake.name = "sink2"} : <i1>
    %21:3 = lazy_fork [3] %result_10 {handshake.bb = 2 : ui32, handshake.name = "lazy_fork1"} : <>
    %22 = constant %21#2 {handshake.bb = 2 : ui32, handshake.name = "constant2", value = 0 : i32} : <>, <i32>
    %addressResult_12, %dataResult_13 = store[%20] %22 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store1"} : <i2>, <i32>, <i2>, <i32>
    %23 = br %17 {handshake.bb = 2 : ui32, handshake.name = "br1"} : <i32>
    %24 = br %19#1 {handshake.bb = 2 : ui32, handshake.name = "br2"} : <i32>
    %25 = br %21#1 {handshake.bb = 2 : ui32, handshake.name = "br3"} : <>
    %26 = mux %29#0 [%falseResult_5, %23] {handshake.bb = 3 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %27:2 = fork [2] %26 {handshake.bb = 3 : ui32, handshake.name = "fork8"} : <i32>
    %28 = mux %29#1 [%falseResult_7, %24] {handshake.bb = 3 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_14, %index_15 = control_merge [%falseResult_9, %25]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %29:2 = fork [2] %index_15 {handshake.bb = 3 : ui32, handshake.name = "fork9"} : <i1>
    %30 = source {handshake.bb = 3 : ui32, handshake.name = "source0"} : <>
    %31 = constant %30 {handshake.bb = 3 : ui32, handshake.name = "constant3", value = 1 : i32} : <>, <i32>
    %32 = addi %28, %31 {handshake.bb = 3 : ui32, handshake.name = "addi0"} : <i32>
    %33:2 = fork [2] %32 {handshake.bb = 3 : ui32, handshake.name = "fork10"} : <i32>
    %34 = cmpi slt, %33#1, %27#1 {handshake.bb = 3 : ui32, handshake.name = "cmpi2"} : <i32>
    %35:3 = fork [3] %34 {handshake.bb = 3 : ui32, handshake.name = "fork11"} : <i1>
    %trueResult_16, %falseResult_17 = cond_br %35#2, %33#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    sink %falseResult_17 {handshake.name = "sink3"} : <i32>
    %trueResult_18, %falseResult_19 = cond_br %35#1, %27#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    sink %falseResult_19 {handshake.name = "sink4"} : <i32>
    %trueResult_20, %falseResult_21 = cond_br %35#0, %result_14 {handshake.bb = 3 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %result_22, %index_23 = control_merge [%falseResult_3, %falseResult_21]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    sink %index_23 {handshake.name = "sink5"} : <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %2#1, %0#1 : <>, <>
  }
}

