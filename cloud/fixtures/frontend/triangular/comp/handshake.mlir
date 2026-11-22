module {
  handshake.func @triangular(%arg0: memref<10xi32>, %arg1: !handshake.channel<i32>, %arg2: memref<100xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["x", "n", "a", "x_start", "a_start", "start"], resNames = ["x_end", "a_end", "end"]} {
    %outputs:2, %memEnd = mem_controller[%arg2 : memref<100xi32>] %arg4 (%24, %addressResult, %0#1, %0#2, %0#3) %result_40 {connectedBlocks = [3 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %0:4 = lsq[MC] (%result_24, %addressResult_28, %addressResult_30, %dataResult_31, %outputs#1)  {groupSizes = [2 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>)
    %outputs_0, %memEnd_1 = mem_controller[%arg0 : memref<10xi32>] %arg3 (%addressResult_26) %result_40 {connectedBlocks = [3 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %1 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %2 = constant %1 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = -1 : i32} : <>, <i32>
    %3 = source {handshake.bb = 0 : ui32, handshake.name = "source1"} : <>
    %4 = constant %3 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 0 : i32} : <>, <i32>
    %5 = addi %arg1, %2 {handshake.bb = 0 : ui32, handshake.name = "addi0"} : <i32>
    %6 = cmpi sgt, %arg1, %4 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %6, %5 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %6, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %6, %arg5 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <>
    %7 = mux %index [%falseResult_19, %falseResult_35] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %8 = mux %index [%falseResult_21, %falseResult_37] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%falseResult_23, %falseResult_39]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %9 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %10 = constant %9 {handshake.bb = 1 : ui32, handshake.name = "constant6", value = 0 : i32} : <>, <i32>
    %11 = source {handshake.bb = 1 : ui32, handshake.name = "source3"} : <>
    %12 = constant %11 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = -1 : i32} : <>, <i32>
    %13 = addi %8, %12 {handshake.bb = 1 : ui32, handshake.name = "addi1"} : <i32>
    %14 = cmpi sgt, %8, %10 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_6, %falseResult_7 = cond_br %14, %13 {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_8, %falseResult_9 = cond_br %14, %8 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %14, %7 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %14, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %15 = mux %index_15 [%trueResult, %trueResult_6] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %16 = mux %index_15 [%trueResult_2, %trueResult_8] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %17 = mux %index_15 [%trueResult_2, %trueResult_10] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %result_14, %index_15 = control_merge [%trueResult_4, %trueResult_12]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %18 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %19 = constant %18 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = -2 : i32} : <>, <i32>
    %20 = source {handshake.bb = 2 : ui32, handshake.name = "source5"} : <>
    %21 = constant %20 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = -1 : i32} : <>, <i32>
    %22 = addi %16, %19 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i32>
    %23 = cmpi sgt, %22, %21 {handshake.bb = 2 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_16, %falseResult_17 = cond_br %23, %22 {handshake.bb = 2 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %23, %17 {handshake.bb = 2 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_20, %falseResult_21 = cond_br %23, %15 {handshake.bb = 2 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_22, %falseResult_23 = cond_br %23, %result_14 {handshake.bb = 2 : ui32, handshake.name = "cond_br14"} : <i1>, <>
    %24 = constant %result_24 {handshake.bb = 3 : ui32, handshake.name = "constant2", value = 1 : i32} : <>, <i32>
    %25 = mux %index_25 [%trueResult_16, %trueResult_32] {handshake.bb = 3 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %26 = mux %index_25 [%trueResult_18, %trueResult_34] {handshake.bb = 3 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %27 = mux %index_25 [%trueResult_20, %trueResult_36] {handshake.bb = 3 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %result_24, %index_25 = control_merge [%trueResult_22, %trueResult_38]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %28 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %29 = constant %28 {handshake.bb = 3 : ui32, handshake.name = "constant10", value = -1 : i32} : <>, <i32>
    %30 = source {handshake.bb = 3 : ui32, handshake.name = "source7"} : <>
    %31 = constant %30 {handshake.bb = 3 : ui32, handshake.name = "constant11", value = 3 : i64} : <>, <i64>
    %32 = source {handshake.bb = 3 : ui32, handshake.name = "source8"} : <>
    %33 = constant %32 {handshake.bb = 3 : ui32, handshake.name = "constant12", value = 1 : i64} : <>, <i64>
    %34 = extsi %25 {handshake.bb = 3 : ui32, handshake.name = "extsi0"} : <i32> to <i64>
    %35 = extsi %27 {handshake.bb = 3 : ui32, handshake.name = "extsi1"} : <i32> to <i64>
    %36 = shli %34, %33 {handshake.bb = 3 : ui32, handshake.name = "shli0"} : <i64>
    %37 = shli %34, %31 {handshake.bb = 3 : ui32, handshake.name = "shli1"} : <i64>
    %38 = addi %36, %37 {handshake.bb = 3 : ui32, handshake.name = "addi6"} : <i64>
    %39 = addi %38, %35 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i64>
    %40 = trunci %39 {handshake.bb = 3 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%40] %outputs#0 {handshake.bb = 3 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %41 = trunci %27 {handshake.bb = 3 : ui32, handshake.name = "index_cast1"} : <i32> to <i32>
    %addressResult_26, %dataResult_27 = load[%41] %outputs_0 {handshake.bb = 3 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %42 = muli %dataResult, %dataResult_27 {handshake.bb = 3 : ui32, handshake.name = "muli1"} : <i32>
    %43 = extsi %25 {handshake.bb = 3 : ui32, handshake.name = "extsi3"} : <i32> to <i64>
    %44 = extsi %26 {handshake.bb = 3 : ui32, handshake.name = "extsi4"} : <i32> to <i64>
    %45 = shli %43, %33 {handshake.bb = 3 : ui32, handshake.name = "shli2"} : <i64>
    %46 = shli %43, %31 {handshake.bb = 3 : ui32, handshake.name = "shli3"} : <i64>
    %47 = addi %45, %46 {handshake.bb = 3 : ui32, handshake.name = "addi7"} : <i64>
    %48 = addi %47, %44 {handshake.bb = 3 : ui32, handshake.name = "addi4"} : <i64>
    %49 = trunci %48 {handshake.bb = 3 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_28, %dataResult_29 = load[%49] %0#0 {handshake.bb = 3 : ui32, handshake.name = "load2"} : <i32>, <i32>, <i32>, <i32>
    %50 = subi %dataResult_29, %42 {handshake.bb = 3 : ui32, handshake.name = "subi0"} : <i32>
    %51 = trunci %48 {handshake.bb = 3 : ui32, handshake.name = "index_cast3"} : <i64> to <i32>
    %addressResult_30, %dataResult_31 = store[%51] %50 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store3"} : <i32>, <i32>, <i32>, <i32>
    %52 = addi %25, %29 {handshake.bb = 3 : ui32, handshake.name = "addi5"} : <i32>
    %53 = cmpi sgt, %52, %29 {handshake.bb = 3 : ui32, handshake.name = "cmpi3"} : <i32>
    %trueResult_32, %falseResult_33 = cond_br %53, %52 {handshake.bb = 3 : ui32, handshake.name = "cond_br15"} : <i1>, <i32>
    %trueResult_34, %falseResult_35 = cond_br %53, %26 {handshake.bb = 3 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    %trueResult_36, %falseResult_37 = cond_br %53, %27 {handshake.bb = 3 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    %trueResult_38, %falseResult_39 = cond_br %53, %result_24 {handshake.bb = 3 : ui32, handshake.name = "cond_br18"} : <i1>, <>
    %result_40, %index_41 = control_merge [%falseResult_5, %falseResult_13]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %memEnd_1, %memEnd, %arg5 : <>, <>, <>
  }
}

