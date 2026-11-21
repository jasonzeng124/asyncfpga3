module {
  handshake.func @test_internal_array(%arg0: memref<640xi32>, %arg1: memref<640xi32>, %arg2: memref<640xi32>, %arg3: memref<640xi32>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, %arg8: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["A", "B", "C", "result", "A_start", "B_start", "C_start", "result_start", "start"], resNames = ["A_end", "B_end", "C_end", "result_end", "end"]} {
    %0:2 = lsq[%2 : memref<640xi32>] (%arg8, %result_5, %addressResult_9, %dataResult_10, %result_31, %addressResult_33, %result_57)  {groupSizes = [1 : i32, 1 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.control<>)
    %memEnd = mem_controller[%arg3 : memref<640xi32>] %arg7 (%61, %addressResult_37, %dataResult_38) %result_57 {connectedBlocks = [5 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> ()
    %outputs, %memEnd_0 = mem_controller[%arg2 : memref<640xi32>] %arg6 (%addressResult_35) %result_57 {connectedBlocks = [5 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_1, %memEnd_2 = mem_controller[%arg1 : memref<640xi32>] %arg5 (%addressResult_7) %result_57 {connectedBlocks = [2 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_3, %memEnd_4 = mem_controller[%arg0 : memref<640xi32>] %arg4 (%addressResult) %result_57 {connectedBlocks = [2 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %1 = constant %arg8 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 0 : i32} : <>, <i32>
    %2 = "handshake.ram"() {handshake.name = "ram0", initialValue = dense<0> : memref<640xi32>} : () -> memref<640xi32>
    %3 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i32>
    %4 = br %arg8 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %5 = mux %index [%3, %trueResult_23] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%4, %trueResult_25]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %6 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant2", value = 0 : i32} : <>, <i32>
    %7 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %8 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %9 = extui %5 {handshake.bb = 1 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %10 = br %6 {handshake.bb = 1 : ui32, handshake.name = "br5"} : <i32>
    %11 = br %5 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i32>
    %12 = br %7 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i64>
    %13 = br %8 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <i64>
    %14 = br %9 {handshake.bb = 1 : ui32, handshake.name = "br9"} : <i64>
    %15 = br %result {handshake.bb = 1 : ui32, handshake.name = "br10"} : <>
    %16 = mux %index_6 [%10, %trueResult] {handshake.bb = 2 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %17 = mux %index_6 [%11, %trueResult_11] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %18 = mux %index_6 [%12, %trueResult_13] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i64>, <i64>] to <i64>
    %19 = mux %index_6 [%13, %trueResult_15] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i64>, <i64>] to <i64>
    %20 = mux %index_6 [%14, %trueResult_17] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<i64>, <i64>] to <i64>
    %result_5, %index_6 = control_merge [%15, %trueResult_19]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %21 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %22 = constant %21 {handshake.bb = 2 : ui32, handshake.name = "constant6", value = 32 : i32} : <>, <i32>
    %23 = source {handshake.bb = 2 : ui32, handshake.name = "source1"} : <>
    %24 = constant %23 {handshake.bb = 2 : ui32, handshake.name = "constant7", value = 1 : i32} : <>, <i32>
    %25 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %26 = constant %25 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = 5 : i64} : <>, <i64>
    %27 = extui %16 {handshake.bb = 2 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %28 = shli %18, %26 {handshake.bb = 2 : ui32, handshake.name = "shli0"} : <i64>
    %29 = addi %28, %27 {handshake.bb = 2 : ui32, handshake.name = "addi0"} : <i64>
    %30 = trunci %29 {handshake.bb = 2 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%30] %outputs_3 {handshake.bb = 2 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %31 = extui %16 {handshake.bb = 2 : ui32, handshake.name = "extui4"} : <i32> to <i64>
    %32 = shli %19, %26 {handshake.bb = 2 : ui32, handshake.name = "shli1"} : <i64>
    %33 = addi %32, %31 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i64>
    %34 = trunci %33 {handshake.bb = 2 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_7, %dataResult_8 = load[%34] %outputs_1 {handshake.bb = 2 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %35 = muli %dataResult, %dataResult_8 {handshake.bb = 2 : ui32, handshake.name = "muli0"} : <i32>
    %36 = extui %16 {handshake.bb = 2 : ui32, handshake.name = "extui5"} : <i32> to <i64>
    %37 = shli %20, %26 {handshake.bb = 2 : ui32, handshake.name = "shli2"} : <i64>
    %38 = addi %37, %36 {handshake.bb = 2 : ui32, handshake.name = "addi2"} : <i64>
    %39 = trunci %38 {handshake.bb = 2 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_9, %dataResult_10 = store[%39] %35 {handshake.bb = 2 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : <i32>, <i32>, <i32>, <i32>
    %40 = addi %16, %24 {handshake.bb = 2 : ui32, handshake.name = "addi4"} : <i32>
    %41 = cmpi ult, %40, %22 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %41, %40 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>
    %trueResult_11, %falseResult_12 = cond_br %41, %17 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_13, %falseResult_14 = cond_br %41, %18 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <i64>
    %trueResult_15, %falseResult_16 = cond_br %41, %19 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i64>
    %trueResult_17, %falseResult_18 = cond_br %41, %20 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <i64>
    %trueResult_19, %falseResult_20 = cond_br %41, %result_5 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <>
    %42 = merge %falseResult_12 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i32>
    %result_21, %index_22 = control_merge [%falseResult_20]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %43 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %44 = constant %43 {handshake.bb = 3 : ui32, handshake.name = "constant9", value = 20 : i32} : <>, <i32>
    %45 = constant %result_21 {handshake.bb = 3 : ui32, handshake.name = "constant10", value = 0 : i32} : <>, <i32>
    %46 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %47 = constant %46 {handshake.bb = 3 : ui32, handshake.name = "constant11", value = 1 : i32} : <>, <i32>
    %48 = addi %42, %47 {handshake.bb = 3 : ui32, handshake.name = "addi5"} : <i32>
    %49 = cmpi ult, %48, %44 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_23, %falseResult_24 = cond_br %49, %48 {handshake.bb = 3 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_25, %falseResult_26 = cond_br %49, %result_21 {handshake.bb = 3 : ui32, handshake.name = "cond_br11"} : <i1>, <>
    %trueResult_27, %falseResult_28 = cond_br %49, %45 {handshake.bb = 3 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %50 = mux %index_30 [%falseResult_28, %trueResult_53] {handshake.bb = 4 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %result_29, %index_30 = control_merge [%falseResult_26, %trueResult_55]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %51 = constant %result_29 {handshake.bb = 4 : ui32, handshake.name = "constant12", value = 0 : i32} : <>, <i32>
    %52 = extui %50 {handshake.bb = 4 : ui32, handshake.name = "extui6"} : <i32> to <i64>
    %53 = extui %50 {handshake.bb = 4 : ui32, handshake.name = "extui7"} : <i32> to <i64>
    %54 = extui %50 {handshake.bb = 4 : ui32, handshake.name = "extui8"} : <i32> to <i64>
    %55 = br %51 {handshake.bb = 4 : ui32, handshake.name = "br11"} : <i32>
    %56 = br %50 {handshake.bb = 4 : ui32, handshake.name = "br12"} : <i32>
    %57 = br %52 {handshake.bb = 4 : ui32, handshake.name = "br13"} : <i64>
    %58 = br %53 {handshake.bb = 4 : ui32, handshake.name = "br14"} : <i64>
    %59 = br %54 {handshake.bb = 4 : ui32, handshake.name = "br15"} : <i64>
    %60 = br %result_29 {handshake.bb = 4 : ui32, handshake.name = "br16"} : <>
    %61 = constant %result_31 {handshake.bb = 5 : ui32, handshake.name = "constant0", value = 1 : i32} : <>, <i32>
    %62 = mux %index_32 [%55, %trueResult_39] {handshake.bb = 5 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %63 = mux %index_32 [%56, %trueResult_41] {handshake.bb = 5 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %64 = mux %index_32 [%57, %trueResult_43] {handshake.bb = 5 : ui32, handshake.name = "mux9"} : <i1>, [<i64>, <i64>] to <i64>
    %65 = mux %index_32 [%58, %trueResult_45] {handshake.bb = 5 : ui32, handshake.name = "mux10"} : <i1>, [<i64>, <i64>] to <i64>
    %66 = mux %index_32 [%59, %trueResult_47] {handshake.bb = 5 : ui32, handshake.name = "mux11"} : <i1>, [<i64>, <i64>] to <i64>
    %result_31, %index_32 = control_merge [%60, %trueResult_49]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    %67 = source {handshake.bb = 5 : ui32, handshake.name = "source5"} : <>
    %68 = constant %67 {handshake.bb = 5 : ui32, handshake.name = "constant13", value = 32 : i32} : <>, <i32>
    %69 = source {handshake.bb = 5 : ui32, handshake.name = "source6"} : <>
    %70 = constant %69 {handshake.bb = 5 : ui32, handshake.name = "constant14", value = 1 : i32} : <>, <i32>
    %71 = source {handshake.bb = 5 : ui32, handshake.name = "source7"} : <>
    %72 = constant %71 {handshake.bb = 5 : ui32, handshake.name = "constant15", value = 5 : i64} : <>, <i64>
    %73 = extui %62 {handshake.bb = 5 : ui32, handshake.name = "extui9"} : <i32> to <i64>
    %74 = shli %64, %72 {handshake.bb = 5 : ui32, handshake.name = "shli3"} : <i64>
    %75 = addi %74, %73 {handshake.bb = 5 : ui32, handshake.name = "addi6"} : <i64>
    %76 = trunci %75 {handshake.bb = 5 : ui32, handshake.name = "index_cast3"} : <i64> to <i32>
    %addressResult_33, %dataResult_34 = load[%76] %0#0 {handshake.bb = 5 : ui32, handshake.name = "load3"} : <i32>, <i32>, <i32>, <i32>
    %77 = extui %62 {handshake.bb = 5 : ui32, handshake.name = "extui10"} : <i32> to <i64>
    %78 = shli %65, %72 {handshake.bb = 5 : ui32, handshake.name = "shli4"} : <i64>
    %79 = addi %78, %77 {handshake.bb = 5 : ui32, handshake.name = "addi8"} : <i64>
    %80 = trunci %79 {handshake.bb = 5 : ui32, handshake.name = "index_cast4"} : <i64> to <i32>
    %addressResult_35, %dataResult_36 = load[%80] %outputs {handshake.bb = 5 : ui32, handshake.name = "load4"} : <i32>, <i32>, <i32>, <i32>
    %81 = muli %dataResult_34, %dataResult_36 {handshake.bb = 5 : ui32, handshake.name = "muli3"} : <i32>
    %82 = extui %62 {handshake.bb = 5 : ui32, handshake.name = "extui11"} : <i32> to <i64>
    %83 = shli %66, %72 {handshake.bb = 5 : ui32, handshake.name = "shli5"} : <i64>
    %84 = addi %83, %82 {handshake.bb = 5 : ui32, handshake.name = "addi9"} : <i64>
    %85 = trunci %84 {handshake.bb = 5 : ui32, handshake.name = "index_cast5"} : <i64> to <i32>
    %addressResult_37, %dataResult_38 = store[%85] %81 {handshake.bb = 5 : ui32, handshake.name = "store5"} : <i32>, <i32>, <i32>, <i32>
    %86 = addi %62, %70 {handshake.bb = 5 : ui32, handshake.name = "addi10"} : <i32>
    %87 = cmpi ult, %86, %68 {handshake.bb = 5 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_39, %falseResult_40 = cond_br %87, %86 {handshake.bb = 5 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_41, %falseResult_42 = cond_br %87, %63 {handshake.bb = 5 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_43, %falseResult_44 = cond_br %87, %64 {handshake.bb = 5 : ui32, handshake.name = "cond_br15"} : <i1>, <i64>
    %trueResult_45, %falseResult_46 = cond_br %87, %65 {handshake.bb = 5 : ui32, handshake.name = "cond_br16"} : <i1>, <i64>
    %trueResult_47, %falseResult_48 = cond_br %87, %66 {handshake.bb = 5 : ui32, handshake.name = "cond_br17"} : <i1>, <i64>
    %trueResult_49, %falseResult_50 = cond_br %87, %result_31 {handshake.bb = 5 : ui32, handshake.name = "cond_br18"} : <i1>, <>
    %88 = merge %falseResult_42 {handshake.bb = 6 : ui32, handshake.name = "merge1"} : <i32>
    %result_51, %index_52 = control_merge [%falseResult_50]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>] to <>, <i1>
    %89 = source {handshake.bb = 6 : ui32, handshake.name = "source8"} : <>
    %90 = constant %89 {handshake.bb = 6 : ui32, handshake.name = "constant16", value = 20 : i32} : <>, <i32>
    %91 = source {handshake.bb = 6 : ui32, handshake.name = "source9"} : <>
    %92 = constant %91 {handshake.bb = 6 : ui32, handshake.name = "constant17", value = 1 : i32} : <>, <i32>
    %93 = addi %88, %92 {handshake.bb = 6 : ui32, handshake.name = "addi11"} : <i32>
    %94 = cmpi ult, %93, %90 {handshake.bb = 6 : ui32, handshake.name = "cmpi3"} : <i32>
    %trueResult_53, %falseResult_54 = cond_br %94, %93 {handshake.bb = 6 : ui32, handshake.name = "cond_br19"} : <i1>, <i32>
    %trueResult_55, %falseResult_56 = cond_br %94, %result_51 {handshake.bb = 6 : ui32, handshake.name = "cond_br20"} : <i1>, <>
    %result_57, %index_58 = control_merge [%falseResult_56]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>] to <>, <i1>
    end {handshake.bb = 7 : ui32, handshake.name = "end0"} %memEnd_4, %memEnd_2, %memEnd_0, %memEnd, %arg8 : <>, <>, <>, <>, <>
  }
}

