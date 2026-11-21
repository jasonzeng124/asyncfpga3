module {
  handshake.func @bicg(%arg0: memref<900xi32>, %arg1: memref<30xi32>, %arg2: memref<30xi32>, %arg3: memref<30xi32>, %arg4: memref<30xi32>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, %arg8: !handshake.control<>, %arg9: !handshake.control<>, %arg10: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["a", "s", "q", "p", "r", "a_start", "s_start", "q_start", "p_start", "r_start", "start"], resNames = ["out0", "a_end", "s_end", "q_end", "p_end", "r_end", "end"]} {
    %outputs, %memEnd = mem_controller[%arg4 : memref<30xi32>] %arg9 (%addressResult_12) %result_38 {connectedBlocks = [2 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_0, %memEnd_1 = mem_controller[%arg3 : memref<30xi32>] %arg8 (%addressResult_16) %result_38 {connectedBlocks = [2 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_2, %memEnd_3 = mem_controller[%arg2 : memref<30xi32>] %arg7 (%addressResult, %56, %addressResult_30, %dataResult_31) %result_38 {connectedBlocks = [1 : i32, 3 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> !handshake.channel<i32>
    %0:2 = lsq[%arg1 : memref<30xi32>] (%arg6, %result_6, %addressResult_10, %addressResult_14, %dataResult_15, %result_38)  {groupSizes = [2 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %outputs_4, %memEnd_5 = mem_controller[%arg0 : memref<900xi32>] %arg5 (%addressResult_8) %result_38 {connectedBlocks = [2 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %1 = constant %arg10 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %3 = br %arg10 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <>
    %4 = mux %index [%2, %trueResult_32] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%3, %trueResult_34]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %5 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant8", value = 0 : i32} : <>, <i32>
    %6 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %7 = trunci %6 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%7] %outputs_2 {handshake.bb = 1 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %8 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %9 = extui %4 {handshake.bb = 1 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %10 = br %5 {handshake.bb = 1 : ui32, handshake.name = "br4"} : <i32>
    %11 = br %dataResult {handshake.bb = 1 : ui32, handshake.name = "br5"} : <i32>
    %12 = br %4 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i32>
    %13 = br %8 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i64>
    %14 = br %9 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <i64>
    %15 = br %result {handshake.bb = 1 : ui32, handshake.name = "br9"} : <>
    %16 = mux %index_7 [%10, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %17 = mux %index_7 [%11, %trueResult_18] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %18 = mux %index_7 [%12, %trueResult_20] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %19 = mux %index_7 [%13, %trueResult_22] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i64>, <i64>] to <i64>
    %20 = mux %index_7 [%14, %trueResult_24] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<i64>, <i64>] to <i64>
    %result_6, %index_7 = control_merge [%15, %trueResult_26]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %21 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %22 = constant %21 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 30 : i32} : <>, <i32>
    %23 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %24 = constant %23 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 1 : i32} : <>, <i32>
    %25 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %26 = constant %25 {handshake.bb = 2 : ui32, handshake.name = "constant11", value = 4 : i64} : <>, <i64>
    %27 = source {handshake.bb = 2 : ui32, handshake.name = "source3"} : <>
    %28 = constant %27 {handshake.bb = 2 : ui32, handshake.name = "constant12", value = 3 : i64} : <>, <i64>
    %29 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %30 = constant %29 {handshake.bb = 2 : ui32, handshake.name = "constant13", value = 2 : i64} : <>, <i64>
    %31 = source {handshake.bb = 2 : ui32, handshake.name = "source5"} : <>
    %32 = constant %31 {handshake.bb = 2 : ui32, handshake.name = "constant14", value = 1 : i64} : <>, <i64>
    %33 = extui %16 {handshake.bb = 2 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %34 = shli %19, %32 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %35 = shli %19, %30 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %36 = addi %34, %35 {handshake.bb = 2 : ui32, handshake.name = "addi5"} : <i64>
    %37 = shli %19, %28 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i64>
    %38 = shli %19, %26 {handshake.bb = 2 : ui32, handshake.name = "shli3"} : <i64>
    %39 = addi %37, %38 {handshake.bb = 2 : ui32, handshake.name = "addi6"} : <i64>
    %40 = addi %36, %39 {handshake.bb = 2 : ui32, handshake.name = "addi7"} : <i64>
    %41 = addi %40, %33 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i64>
    %42 = trunci %41 {handshake.bb = 2 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_8, %dataResult_9 = load[%42] %outputs_4 {handshake.bb = 2 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %43 = extui %16 {handshake.bb = 2 : ui32, handshake.name = "extui4"} : <i32> to <i64>
    %44 = trunci %43 {handshake.bb = 2 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_10, %dataResult_11 = load[%44] %0#0 {handshake.bb = 2 : ui32, handshake.name = "load2"} : <i32>, <i32>, <i32>, <i32>
    %45 = trunci %20 {handshake.bb = 2 : ui32, handshake.name = "index_cast3"} : <i64> to <i32>
    %addressResult_12, %dataResult_13 = load[%45] %outputs {handshake.bb = 2 : ui32, handshake.name = "load3"} : <i32>, <i32>, <i32>, <i32>
    %46 = muli %dataResult_13, %dataResult_9 {handshake.bb = 2 : ui32, handshake.name = "muli1"} : <i32>
    %47 = addi %dataResult_11, %46 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %48 = extui %16 {handshake.bb = 2 : ui32, handshake.name = "extui5"} : <i32> to <i64>
    %49 = trunci %48 {handshake.bb = 2 : ui32, handshake.name = "index_cast4"} : <i64> to <i32>
    %addressResult_14, %dataResult_15 = store[%49] %47 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store4"} : <i32>, <i32>, <i32>, <i32>
    %50 = extui %16 {handshake.bb = 2 : ui32, handshake.name = "extui6"} : <i32> to <i64>
    %51 = trunci %50 {handshake.bb = 2 : ui32, handshake.name = "index_cast5"} : <i64> to <i32>
    %addressResult_16, %dataResult_17 = load[%51] %outputs_0 {handshake.bb = 2 : ui32, handshake.name = "load5"} : <i32>, <i32>, <i32>, <i32>
    %52 = muli %dataResult_9, %dataResult_17 {handshake.bb = 2 : ui32, handshake.name = "muli2"} : <i32>
    %53 = addi %17, %52 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i32>
    %54 = addi %16, %24 {handshake.bb = 2 : ui32, handshake.name = "addi3"} : <i32>
    %55 = cmpi ult, %54, %22 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %55, %54 {handshake.bb = 2 : ui32, handshake.name = "cond_br2"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %55, %53 {handshake.bb = 2 : ui32, handshake.name = "cond_br3"} : <i1>, <i32>
    %trueResult_20, %falseResult_21 = cond_br %55, %18 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_22, %falseResult_23 = cond_br %55, %19 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i64>
    %trueResult_24, %falseResult_25 = cond_br %55, %20 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <i64>
    %trueResult_26, %falseResult_27 = cond_br %55, %result_6 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <>
    %56 = constant %result_28 {handshake.bb = 3 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %57 = merge %falseResult_19 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i32>
    %58 = merge %falseResult_21 {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <i32>
    %result_28, %index_29 = control_merge [%falseResult_27]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %59 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %60 = constant %59 {handshake.bb = 3 : ui32, handshake.name = "constant15", value = 30 : i32} : <>, <i32>
    %61 = source {handshake.bb = 3 : ui32, handshake.name = "source7"} : <>
    %62 = constant %61 {handshake.bb = 3 : ui32, handshake.name = "constant16", value = 1 : i32} : <>, <i32>
    %63 = extui %58 {handshake.bb = 3 : ui32, handshake.name = "extui7"} : <i32> to <i64>
    %64 = trunci %63 {handshake.bb = 3 : ui32, handshake.name = "index_cast6"} : <i64> to <i32>
    %addressResult_30, %dataResult_31 = store[%64] %57 {handshake.bb = 3 : ui32, handshake.name = "store6"} : <i32>, <i32>, <i32>, <i32>
    %65 = addi %58, %62 {handshake.bb = 3 : ui32, handshake.name = "addi4"} : <i32>
    %66 = cmpi ult, %65, %60 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_32, %falseResult_33 = cond_br %66, %65 {handshake.bb = 3 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_34, %falseResult_35 = cond_br %66, %result_28 {handshake.bb = 3 : ui32, handshake.name = "cond_br9"} : <i1>, <>
    %trueResult_36, %falseResult_37 = cond_br %66, %57 {handshake.bb = 3 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %67 = merge %falseResult_37 {handshake.bb = 4 : ui32, handshake.name = "merge2"} : <i32>
    %result_38, %index_39 = control_merge [%falseResult_35]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    end {handshake.bb = 4 : ui32, handshake.name = "end0"} %67, %memEnd_5, %0#1, %memEnd_3, %memEnd_1, %memEnd, %arg10 : <i32>, <>, <>, <>, <>, <>, <>
  }
}

