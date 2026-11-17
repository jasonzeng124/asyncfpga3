module {
  handshake.func @insertion_sort(%arg0: memref<30xi32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, %arg3: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>) attributes {argNames = ["A", "n", "A_start", "start"], resNames = ["A_end", "end"]} {
    %0:4 = lsq[%arg0 : memref<30xi32>] (%arg2, %result, %addressResult, %result_4, %addressResult_6, %result_18, %addressResult_20, %addressResult_22, %dataResult_23, %result_36, %addressResult_38, %dataResult_39, %result_46)  {groupSizes = [1 : i32, 1 : i32, 2 : i32, 1 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>)
    %1 = constant %arg3 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 1 : i32} : <>, <i32>
    %2 = cmpi sgt, %arg1, %1 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %2, %1 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %2, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %2, %arg3 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %3 = mux %index [%trueResult, %trueResult_40] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %4 = mux %index [%trueResult_0, %trueResult_42] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_2, %trueResult_44]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %5 = extui %3 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %6 = trunci %5 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%6] %0#0 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %7 = br %3 {handshake.bb = 1 : ui32, handshake.name = "br1"} : <i32>
    %8 = br %4 {handshake.bb = 1 : ui32, handshake.name = "br2"} : <i32>
    %9 = br %dataResult {handshake.bb = 1 : ui32, handshake.name = "br3"} : <i32>
    %10 = br %result {handshake.bb = 1 : ui32, handshake.name = "br4"} : <>
    %11 = mux %index_5 [%7, %trueResult_24] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %12 = mux %index_5 [%8, %trueResult_26] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %13 = mux %index_5 [%7, %trueResult_28] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %14 = mux %index_5 [%9, %trueResult_30] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %result_4, %index_5 = control_merge [%10, %trueResult_32]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %15 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %16 = constant %15 {handshake.bb = 2 : ui32, handshake.name = "constant3", value = -1 : i32} : <>, <i32>
    %17 = addi %11, %16 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i32>
    %18 = trunci %17 {handshake.bb = 2 : ui32, handshake.name = "index_cast1"} : <i32> to <i32>
    %addressResult_6, %dataResult_7 = load[%18] %0#1 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %19 = cmpi sgt, %dataResult_7, %14 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_8, %falseResult_9 = cond_br %19, %12 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %19, %13 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %19, %14 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %19, %11 {handshake.bb = 2 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %19, %result_4 {handshake.bb = 2 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %20 = merge %trueResult_8 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i32>
    %21 = merge %trueResult_10 {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <i32>
    %22 = merge %trueResult_12 {handshake.bb = 3 : ui32, handshake.name = "merge2"} : <i32>
    %23 = merge %trueResult_14 {handshake.bb = 3 : ui32, handshake.name = "merge3"} : <i32>
    %result_18, %index_19 = control_merge [%trueResult_16]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %24 = constant %result_18 {handshake.bb = 3 : ui32, handshake.name = "constant4", value = 0 : i32} : <>, <i32>
    %25 = source {handshake.bb = 3 : ui32, handshake.name = "source1"} : <>
    %26 = constant %25 {handshake.bb = 3 : ui32, handshake.name = "constant5", value = -1 : i32} : <>, <i32>
    %27 = addi %23, %26 {handshake.bb = 3 : ui32, handshake.name = "addi1"} : <i32>
    %28 = trunci %27 {handshake.bb = 3 : ui32, handshake.name = "index_cast2"} : <i32> to <i32>
    %addressResult_20, %dataResult_21 = load[%28] %0#2 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load2"} : <i32>, <i32>, <i32>, <i32>
    %29 = trunci %23 {handshake.bb = 3 : ui32, handshake.name = "index_cast3"} : <i32> to <i32>
    %addressResult_22, %dataResult_23 = store[%29] %dataResult_21 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store3"} : <i32>, <i32>, <i32>, <i32>
    %30 = addi %23, %26 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i32>
    %31 = cmpi sgt, %30, %24 {handshake.bb = 3 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_24, %falseResult_25 = cond_br %31, %30 {handshake.bb = 3 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_26, %falseResult_27 = cond_br %31, %20 {handshake.bb = 3 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_28, %falseResult_29 = cond_br %31, %21 {handshake.bb = 3 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_30, %falseResult_31 = cond_br %31, %22 {handshake.bb = 3 : ui32, handshake.name = "cond_br15"} : <i1>, <i32>
    %trueResult_32, %falseResult_33 = cond_br %31, %result_18 {handshake.bb = 3 : ui32, handshake.name = "cond_br16"} : <i1>, <>
    %trueResult_34, %falseResult_35 = cond_br %31, %24 {handshake.bb = 3 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    %32 = mux %index_37 [%falseResult_15, %falseResult_35] {handshake.bb = 4 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %33 = mux %index_37 [%falseResult_9, %falseResult_27] {handshake.bb = 4 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %34 = mux %index_37 [%falseResult_11, %falseResult_29] {handshake.bb = 4 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %35 = mux %index_37 [%falseResult_13, %falseResult_31] {handshake.bb = 4 : ui32, handshake.name = "mux9"} : <i1>, [<i32>, <i32>] to <i32>
    %result_36, %index_37 = control_merge [%falseResult_17, %falseResult_33]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %36 = source {handshake.bb = 4 : ui32, handshake.name = "source2"} : <>
    %37 = constant %36 {handshake.bb = 4 : ui32, handshake.name = "constant6", value = 1 : i32} : <>, <i32>
    %38 = trunci %32 {handshake.bb = 4 : ui32, handshake.name = "index_cast4"} : <i32> to <i32>
    %addressResult_38, %dataResult_39 = store[%38] %35 {handshake.bb = 4 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store4"} : <i32>, <i32>, <i32>, <i32>
    %39 = addi %34, %37 {handshake.bb = 4 : ui32, handshake.name = "addi3"} : <i32>
    %40 = cmpi slt, %39, %33 {handshake.bb = 4 : ui32, handshake.name = "cmpi3"} : <i32>
    %trueResult_40, %falseResult_41 = cond_br %40, %39 {handshake.bb = 4 : ui32, handshake.name = "cond_br18"} : <i1>, <i32>
    %trueResult_42, %falseResult_43 = cond_br %40, %33 {handshake.bb = 4 : ui32, handshake.name = "cond_br19"} : <i1>, <i32>
    %trueResult_44, %falseResult_45 = cond_br %40, %result_36 {handshake.bb = 4 : ui32, handshake.name = "cond_br20"} : <i1>, <>
    %result_46, %index_47 = control_merge [%falseResult_3, %falseResult_45]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 5 : ui32, handshake.name = "end0"} %0#3, %arg3 : <>, <>
  }
}

