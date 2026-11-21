module {
  handshake.func @loop_array(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: memref<10xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["n", "k", "c", "c_start", "start"], resNames = ["c_end", "end"]} {
    %0:4 = fork [4] %arg4 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg0 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2:2 = lsq[%arg2 : memref<10xi32>] (%arg3, %18#0, %addressResult, %addressResult_6, %dataResult_7, %result_16)  {groupSizes = [2 : i32], handshake.name = "lsq1"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i4>, !handshake.channel<i4>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %3 = constant %0#3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 1 : i32} : <>, <i32>
    %4 = cmpi sgt, %1#1, %3 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %5:4 = fork [4] %4 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %6 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = true} : <>, <i1>
    %trueResult, %falseResult = cond_br %5#0, %6 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i1>
    sink %falseResult {handshake.name = "sink0"} : <i1>
    %7 = extui %trueResult {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i1> to <i32>
    %trueResult_0, %falseResult_1 = cond_br %5#3, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    sink %falseResult_1 {handshake.name = "sink1"} : <i32>
    %trueResult_2, %falseResult_3 = cond_br %5#2, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    sink %falseResult_3 {handshake.name = "sink2"} : <i32>
    %trueResult_4, %falseResult_5 = cond_br %5#1, %0#2 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %8 = mux %17#0 [%7, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %9:3 = fork [3] %8 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %10 = trunci %9#0 {handshake.bb = 1 : ui32, handshake.name = "trunci0"} : <i32> to <i4>
    %11 = constant %19 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = -1 : i4} : <>, <i4>
    %12 = trunci %9#1 {handshake.bb = 1 : ui32, handshake.name = "trunci1"} : <i32> to <i4>
    %13 = mux %17#1 [%trueResult_0, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %14:2 = fork [2] %13 {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i32>
    %15 = mux %17#2 [%trueResult_2, %trueResult_12] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %16:2 = fork [2] %15 {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <i32>
    %result, %index = control_merge [%trueResult_4, %trueResult_14]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %17:3 = fork [3] %index {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i1>
    %18:2 = fork [2] %result {handshake.bb = 1 : ui32, handshake.name = "fork7"} : <>
    %19 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %20 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %21 = constant %20 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 1 : i32} : <>, <i32>
    %22 = addi %10, %11 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i4>
    %addressResult, %dataResult = load[%22] %2#0 {handshake.bb = 1 : ui32, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "load0"} : <i4>, <i32>, <i4>, <i32>
    %23 = addi %dataResult, %16#1 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %addressResult_6, %dataResult_7 = store[%12] %23 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store1"} : <i4>, <i32>, <i4>, <i32>
    %24 = addi %9#2, %21 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %25:2 = fork [2] %24 {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <i32>
    %26 = cmpi slt, %25#1, %14#1 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %27:4 = fork [4] %26 {handshake.bb = 1 : ui32, handshake.name = "fork9"} : <i1>
    %trueResult_8, %falseResult_9 = cond_br %27#3, %25#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    sink %falseResult_9 {handshake.name = "sink3"} : <i32>
    %trueResult_10, %falseResult_11 = cond_br %27#2, %14#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    sink %falseResult_11 {handshake.name = "sink4"} : <i32>
    %trueResult_12, %falseResult_13 = cond_br %27#1, %16#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    sink %falseResult_13 {handshake.name = "sink5"} : <i32>
    %trueResult_14, %falseResult_15 = cond_br %27#0, %18#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <>
    %result_16, %index_17 = control_merge [%falseResult_5, %falseResult_15]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    sink %index_17 {handshake.name = "sink6"} : <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %2#1, %0#1 : <>, <>
  }
}

