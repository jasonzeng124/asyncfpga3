module {
  handshake.func @polyn_mult(%arg0: memref<100xi32>, %arg1: memref<100xi32>, %arg2: memref<100xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "b", "out", "a_start", "b_start", "out_start", "start"], resNames = ["out0", "a_end", "b_end", "out_end", "end"]} {
    %0:3 = lsq[%arg2 : memref<100xi32>] (%arg5, %result, %addressResult, %dataResult, %result_8, %addressResult_14, %addressResult_16, %dataResult_17, %result_28, %addressResult_34, %addressResult_36, %dataResult_37, %result_54)  {groupSizes = [1 : i32, 2 : i32, 2 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>)
    %outputs:2, %memEnd = mem_controller[%arg1 : memref<100xi32>] %arg4 (%addressResult_12, %addressResult_32) %result_54 {connectedBlocks = [2 : i32, 4 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %outputs_0:2, %memEnd_1 = mem_controller[%arg0 : memref<100xi32>] %arg3 (%addressResult_10, %addressResult_30) %result_54 {connectedBlocks = [2 : i32, 4 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %1 = constant %arg6 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %3 = br %arg6 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %4 = mux %index [%2, %trueResult_48] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%3, %trueResult_50]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %5 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 1 : i32} : <>, <i32>
    %6 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %7 = constant %6 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = 100 : i32} : <>, <i32>
    %8 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant5", value = 0 : i32} : <>, <i32>
    %9 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %10 = trunci %9 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = store[%10] %8 {handshake.bb = 1 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load7", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store8", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store0"} : <i32>, <i32>, <i32>, <i32>
    %11 = subi %7, %4 {handshake.bb = 1 : ui32, handshake.name = "subi0"} : <i32>
    %12 = cmpi ugt, %11, %5 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %12, %5 {handshake.bb = 1 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %12, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %12, %11 {handshake.bb = 1 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %12, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %13 = mux %index_9 [%trueResult, %trueResult_18] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %14 = mux %index_9 [%trueResult_2, %trueResult_20] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %15 = mux %index_9 [%trueResult_4, %trueResult_22] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result_8, %index_9 = control_merge [%trueResult_6, %trueResult_24]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %16 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %17 = constant %16 {handshake.bb = 2 : ui32, handshake.name = "constant6", value = 1 : i32} : <>, <i32>
    %18 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %19 = constant %18 {handshake.bb = 2 : ui32, handshake.name = "constant7", value = 100 : i32} : <>, <i32>
    %20 = addi %14, %13 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i32>
    %21 = extui %20 {handshake.bb = 2 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %22 = trunci %21 {handshake.bb = 2 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_10, %dataResult_11 = load[%22] %outputs_0#0 {handshake.bb = 2 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %23 = subi %19, %13 {handshake.bb = 2 : ui32, handshake.name = "subi1"} : <i32>
    %24 = extui %23 {handshake.bb = 2 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %25 = trunci %24 {handshake.bb = 2 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_12, %dataResult_13 = load[%25] %outputs#0 {handshake.bb = 2 : ui32, handshake.name = "load2"} : <i32>, <i32>, <i32>, <i32>
    %26 = muli %dataResult_11, %dataResult_13 {handshake.bb = 2 : ui32, handshake.name = "muli0"} : <i32>
    %27 = extui %14 {handshake.bb = 2 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %28 = trunci %27 {handshake.bb = 2 : ui32, handshake.name = "index_cast3"} : <i64> to <i32>
    %addressResult_14, %dataResult_15 = load[%28] %0#0 {handshake.bb = 2 : ui32, handshake.name = "load3"} : <i32>, <i32>, <i32>, <i32>
    %29 = addi %dataResult_15, %26 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %30 = trunci %27 {handshake.bb = 2 : ui32, handshake.name = "index_cast4"} : <i64> to <i32>
    %addressResult_16, %dataResult_17 = store[%30] %29 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load7", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store8", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store4"} : <i32>, <i32>, <i32>, <i32>
    %31 = addi %13, %17 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i32>
    %32 = cmpi ult, %31, %15 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_18, %falseResult_19 = cond_br %32, %31 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_20, %falseResult_21 = cond_br %32, %14 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_22, %falseResult_23 = cond_br %32, %15 {handshake.bb = 2 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_24, %falseResult_25 = cond_br %32, %result_8 {handshake.bb = 2 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %33 = mux %index_27 [%falseResult_3, %falseResult_21] {handshake.bb = 3 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %result_26, %index_27 = control_merge [%falseResult_7, %falseResult_25]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %34 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %35 = constant %34 {handshake.bb = 3 : ui32, handshake.name = "constant8", value = 1 : i32} : <>, <i32>
    %36 = constant %result_26 {handshake.bb = 3 : ui32, handshake.name = "constant9", value = 0 : i32} : <>, <i32>
    %37 = addi %33, %35 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i32>
    %38 = br %36 {handshake.bb = 3 : ui32, handshake.name = "br4"} : <i32>
    %39 = br %33 {handshake.bb = 3 : ui32, handshake.name = "br5"} : <i32>
    %40 = br %37 {handshake.bb = 3 : ui32, handshake.name = "br6"} : <i32>
    %41 = br %result_26 {handshake.bb = 3 : ui32, handshake.name = "br7"} : <>
    %42 = mux %index_29 [%38, %trueResult_38] {handshake.bb = 4 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %43 = mux %index_29 [%39, %trueResult_40] {handshake.bb = 4 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %44 = mux %index_29 [%40, %trueResult_42] {handshake.bb = 4 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %result_28, %index_29 = control_merge [%41, %trueResult_44]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %45 = source {handshake.bb = 4 : ui32, handshake.name = "source4"} : <>
    %46 = constant %45 {handshake.bb = 4 : ui32, handshake.name = "constant10", value = 1 : i32} : <>, <i32>
    %47 = subi %43, %42 {handshake.bb = 4 : ui32, handshake.name = "subi2"} : <i32>
    %48 = extui %47 {handshake.bb = 4 : ui32, handshake.name = "extui4"} : <i32> to <i64>
    %49 = trunci %48 {handshake.bb = 4 : ui32, handshake.name = "index_cast5"} : <i64> to <i32>
    %addressResult_30, %dataResult_31 = load[%49] %outputs_0#1 {handshake.bb = 4 : ui32, handshake.name = "load5"} : <i32>, <i32>, <i32>, <i32>
    %50 = extui %42 {handshake.bb = 4 : ui32, handshake.name = "extui5"} : <i32> to <i64>
    %51 = trunci %50 {handshake.bb = 4 : ui32, handshake.name = "index_cast6"} : <i64> to <i32>
    %addressResult_32, %dataResult_33 = load[%51] %outputs#1 {handshake.bb = 4 : ui32, handshake.name = "load6"} : <i32>, <i32>, <i32>, <i32>
    %52 = muli %dataResult_31, %dataResult_33 {handshake.bb = 4 : ui32, handshake.name = "muli1"} : <i32>
    %53 = extui %43 {handshake.bb = 4 : ui32, handshake.name = "extui6"} : <i32> to <i64>
    %54 = trunci %53 {handshake.bb = 4 : ui32, handshake.name = "index_cast7"} : <i64> to <i32>
    %addressResult_34, %dataResult_35 = load[%54] %0#1 {handshake.bb = 4 : ui32, handshake.name = "load7"} : <i32>, <i32>, <i32>, <i32>
    %55 = addi %dataResult_35, %52 {handshake.bb = 4 : ui32, handshake.name = "addi4"} : <i32>
    %56 = trunci %53 {handshake.bb = 4 : ui32, handshake.name = "index_cast8"} : <i64> to <i32>
    %addressResult_36, %dataResult_37 = store[%56] %55 {handshake.bb = 4 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load7", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store8"} : <i32>, <i32>, <i32>, <i32>
    %57 = addi %42, %46 {handshake.bb = 4 : ui32, handshake.name = "addi5"} : <i32>
    %58 = cmpi ult, %57, %44 {handshake.bb = 4 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_38, %falseResult_39 = cond_br %58, %57 {handshake.bb = 4 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_40, %falseResult_41 = cond_br %58, %43 {handshake.bb = 4 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_42, %falseResult_43 = cond_br %58, %44 {handshake.bb = 4 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_44, %falseResult_45 = cond_br %58, %result_28 {handshake.bb = 4 : ui32, handshake.name = "cond_br15"} : <i1>, <>
    %59 = merge %falseResult_39 {handshake.bb = 5 : ui32, handshake.name = "merge0"} : <i32>
    %60 = merge %falseResult_41 {handshake.bb = 5 : ui32, handshake.name = "merge1"} : <i32>
    %result_46, %index_47 = control_merge [%falseResult_45]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    %61 = source {handshake.bb = 5 : ui32, handshake.name = "source5"} : <>
    %62 = constant %61 {handshake.bb = 5 : ui32, handshake.name = "constant11", value = 1 : i32} : <>, <i32>
    %63 = source {handshake.bb = 5 : ui32, handshake.name = "source6"} : <>
    %64 = constant %63 {handshake.bb = 5 : ui32, handshake.name = "constant12", value = 100 : i32} : <>, <i32>
    %65 = addi %59, %60 {handshake.bb = 5 : ui32, handshake.name = "addi6"} : <i32>
    %66 = addi %60, %62 {handshake.bb = 5 : ui32, handshake.name = "addi7"} : <i32>
    %67 = cmpi ult, %66, %64 {handshake.bb = 5 : ui32, handshake.name = "cmpi3"} : <i32>
    %trueResult_48, %falseResult_49 = cond_br %67, %66 {handshake.bb = 5 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    %trueResult_50, %falseResult_51 = cond_br %67, %result_46 {handshake.bb = 5 : ui32, handshake.name = "cond_br17"} : <i1>, <>
    %trueResult_52, %falseResult_53 = cond_br %67, %65 {handshake.bb = 5 : ui32, handshake.name = "cond_br18"} : <i1>, <i32>
    %68 = merge %falseResult_53 {handshake.bb = 6 : ui32, handshake.name = "merge2"} : <i32>
    %result_54, %index_55 = control_merge [%falseResult_51]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>] to <>, <i1>
    end {handshake.bb = 6 : ui32, handshake.name = "end0"} %68, %memEnd_1, %memEnd, %0#2, %arg6 : <i32>, <>, <>, <>, <>
  }
}

