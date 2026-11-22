module {
  handshake.func @loop_array(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: memref<10xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["n", "k", "c", "c_start", "start"], resNames = ["c_end", "end"]} {
    %0:2 = lsq[%arg2 : memref<10xi32>] (%arg3, %result, %addressResult, %addressResult_6, %dataResult_7, %result_16)  {groupSizes = [2 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %1 = constant %arg4 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 1 : i32} : <>, <i32>
    %2 = cmpi sgt, %arg0, %1 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %2, %1 {handshake.bb = 0 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %2, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %2, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %2, %arg4 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <>
    %3 = mux %index [%trueResult, %trueResult_8] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %4 = mux %index [%trueResult_0, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %5 = mux %index [%trueResult_2, %trueResult_12] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_4, %trueResult_14]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %6 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %7 = constant %6 {handshake.bb = 1 : ui32, handshake.name = "constant2", value = -1 : i32} : <>, <i32>
    %8 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %9 = constant %8 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 1 : i32} : <>, <i32>
    %10 = addi %3, %7 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>
    %11 = trunci %10 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i32> to <i32>
    %addressResult, %dataResult = load[%11] %0#0 {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %12 = addi %dataResult, %5 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %13 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %14 = trunci %13 {handshake.bb = 1 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_6, %dataResult_7 = store[%14] %12 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : <i32>, <i32>, <i32>, <i32>
    %15 = addi %3, %9 {handshake.bb = 1 : ui32, handshake.name = "addi2"} : <i32>
    %16 = cmpi slt, %15, %4 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_8, %falseResult_9 = cond_br %16, %15 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %16, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %16, %5 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %16, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <>
    %result_16, %index_17 = control_merge [%falseResult_5, %falseResult_15]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 2 : ui32, handshake.name = "end0"} %0#1, %arg4 : <>, <>
  }
}

