module {
  handshake.func @sobel(%arg0: memref<256xi32>, %arg1: memref<9xi32>, %arg2: memref<9xi32>, %arg3: memref<256xi32>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, %arg8: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["in", "gX", "gY", "out", "in_start", "gX_start", "gY_start", "out_start", "start"], resNames = ["out0", "in_end", "gX_end", "gY_end", "out_end", "end"]} {
    %memEnd = mem_controller[%arg3 : memref<256xi32>] %arg7 (%138, %addressResult_93, %dataResult_94) %result_111 {connectedBlocks = [10 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> ()
    %outputs, %memEnd_0 = mem_controller[%arg2 : memref<9xi32>] %arg6 (%addressResult_41) %result_111 {connectedBlocks = [7 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_1, %memEnd_2 = mem_controller[%arg1 : memref<9xi32>] %arg5 (%addressResult_43) %result_111 {connectedBlocks = [7 : i32], handshake.name = "mem_controller2"} :    (!handshake.channel<i32>) -> !handshake.channel<i32>
    %outputs_3:2, %memEnd_4 = mem_controller[%arg0 : memref<256xi32>] %arg4 (%addressResult, %addressResult_35) %result_111 {connectedBlocks = [5 : i32], handshake.name = "mem_controller3"} :    (!handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<i32>, !handshake.channel<i32>)
    %0 = constant %arg8 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = br %0 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <i32>
    %2 = br %arg8 {handshake.bb = 0 : ui32, handshake.name = "br6"} : <>
    %3 = mux %index [%1, %trueResult_105] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %4 = mux %index [%1, %trueResult_107] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%2, %trueResult_109]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %5 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant9", value = 0 : i32} : <>, <i32>
    %6 = br %3 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <i32>
    %7 = br %5 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <i32>
    %8 = br %4 {handshake.bb = 1 : ui32, handshake.name = "br9"} : <i32>
    %9 = br %result {handshake.bb = 1 : ui32, handshake.name = "br10"} : <>
    %10 = mux %index_6 [%6, %trueResult_95] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %11 = mux %index_6 [%7, %trueResult_97] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %12 = mux %index_6 [%8, %trueResult_99] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %result_5, %index_6 = control_merge [%9, %trueResult_101]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %13 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %14 = constant %13 {handshake.bb = 2 : ui32, handshake.name = "constant10", value = 5 : i32} : <>, <i32>
    %15 = cmpi slt, %11, %14 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %15, %12 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_7, %falseResult_8 = cond_br %15, %10 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_9, %falseResult_10 = cond_br %15, %11 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_11, %falseResult_12 = cond_br %15, %result_5 {handshake.bb = 2 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %16 = merge %falseResult {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i32>
    %17 = merge %falseResult_8 {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <i32>
    %18 = merge %falseResult_10 {handshake.bb = 3 : ui32, handshake.name = "merge2"} : <i32>
    %result_13, %index_14 = control_merge [%falseResult_12]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %19 = source {handshake.bb = 3 : ui32, handshake.name = "source1"} : <>
    %20 = constant %19 {handshake.bb = 3 : ui32, handshake.name = "constant11", value = 5 : i32} : <>, <i32>
    %21 = cmpi eq, %18, %20 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_15, %falseResult_16 = cond_br %21, %17 {handshake.bb = 3 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_17, %falseResult_18 = cond_br %21, %16 {handshake.bb = 3 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_19, %falseResult_20 = cond_br %21, %18 {handshake.bb = 3 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_21, %falseResult_22 = cond_br %21, %result_13 {handshake.bb = 3 : ui32, handshake.name = "cond_br14"} : <i1>, <>
    %22 = merge %trueResult {handshake.bb = 4 : ui32, handshake.name = "merge3"} : <i32>
    %23 = merge %trueResult_7 {handshake.bb = 4 : ui32, handshake.name = "merge4"} : <i32>
    %24 = merge %trueResult_9 {handshake.bb = 4 : ui32, handshake.name = "merge5"} : <i32>
    %result_23, %index_24 = control_merge [%trueResult_11]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>] to <>, <i1>
    %25 = source {handshake.bb = 4 : ui32, handshake.name = "source2"} : <>
    %26 = constant %25 {handshake.bb = 4 : ui32, handshake.name = "constant12", value = 0 : i32} : <>, <i32>
    %27 = cmpi eq, %24, %26 {handshake.bb = 4 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_25, %falseResult_26 = cond_br %27, %23 {handshake.bb = 4 : ui32, handshake.name = "cond_br15"} : <i1>, <i32>
    %trueResult_27, %falseResult_28 = cond_br %27, %22 {handshake.bb = 4 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    %trueResult_29, %falseResult_30 = cond_br %27, %24 {handshake.bb = 4 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    %trueResult_31, %falseResult_32 = cond_br %27, %result_23 {handshake.bb = 4 : ui32, handshake.name = "cond_br18"} : <i1>, <>
    %28 = mux %index_34 [%falseResult_18, %falseResult_28] {handshake.bb = 5 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %29 = mux %index_34 [%falseResult_16, %falseResult_26] {handshake.bb = 5 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %30 = mux %index_34 [%falseResult_20, %falseResult_30] {handshake.bb = 5 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %result_33, %index_34 = control_merge [%falseResult_22, %falseResult_32]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    %31 = constant %result_33 {handshake.bb = 5 : ui32, handshake.name = "constant13", value = -1 : i32} : <>, <i32>
    %32 = constant %result_33 {handshake.bb = 5 : ui32, handshake.name = "constant14", value = 0 : i32} : <>, <i32>
    %33 = extui %30 {handshake.bb = 5 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %34 = trunci %33 {handshake.bb = 5 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%34] %outputs_3#0 {handshake.bb = 5 : ui32, handshake.name = "load0"} : <i32>, <i32>, <i32>, <i32>
    %35 = extui %30 {handshake.bb = 5 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %36 = trunci %35 {handshake.bb = 5 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_35, %dataResult_36 = load[%36] %outputs_3#1 {handshake.bb = 5 : ui32, handshake.name = "load1"} : <i32>, <i32>, <i32>, <i32>
    %37 = br %31 {handshake.bb = 5 : ui32, handshake.name = "br11"} : <i32>
    %38 = br %32 {handshake.bb = 5 : ui32, handshake.name = "br12"} : <i32>
    %39 = br %28 {handshake.bb = 5 : ui32, handshake.name = "br13"} : <i32>
    %40 = br %29 {handshake.bb = 5 : ui32, handshake.name = "br14"} : <i32>
    %41 = br %30 {handshake.bb = 5 : ui32, handshake.name = "br15"} : <i32>
    %42 = br %dataResult {handshake.bb = 5 : ui32, handshake.name = "br16"} : <i32>
    %43 = br %dataResult_36 {handshake.bb = 5 : ui32, handshake.name = "br17"} : <i32>
    %44 = br %result_33 {handshake.bb = 5 : ui32, handshake.name = "br18"} : <>
    %45 = mux %index_38 [%37, %trueResult_71] {handshake.bb = 6 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %46 = mux %index_38 [%38, %trueResult_73] {handshake.bb = 6 : ui32, handshake.name = "mux9"} : <i1>, [<i32>, <i32>] to <i32>
    %47 = mux %index_38 [%38, %trueResult_75] {handshake.bb = 6 : ui32, handshake.name = "mux10"} : <i1>, [<i32>, <i32>] to <i32>
    %48 = mux %index_38 [%39, %trueResult_77] {handshake.bb = 6 : ui32, handshake.name = "mux11"} : <i1>, [<i32>, <i32>] to <i32>
    %49 = mux %index_38 [%40, %trueResult_79] {handshake.bb = 6 : ui32, handshake.name = "mux12"} : <i1>, [<i32>, <i32>] to <i32>
    %50 = mux %index_38 [%41, %trueResult_81] {handshake.bb = 6 : ui32, handshake.name = "mux13"} : <i1>, [<i32>, <i32>] to <i32>
    %51 = mux %index_38 [%42, %trueResult_83] {handshake.bb = 6 : ui32, handshake.name = "mux14"} : <i1>, [<i32>, <i32>] to <i32>
    %52 = mux %index_38 [%43, %trueResult_85] {handshake.bb = 6 : ui32, handshake.name = "mux15"} : <i1>, [<i32>, <i32>] to <i32>
    %result_37, %index_38 = control_merge [%44, %trueResult_87]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>, <>] to <>, <i1>
    %53 = source {handshake.bb = 6 : ui32, handshake.name = "source3"} : <>
    %54 = constant %53 {handshake.bb = 6 : ui32, handshake.name = "constant15", value = 1 : i32} : <>, <i32>
    %55 = constant %result_37 {handshake.bb = 6 : ui32, handshake.name = "constant16", value = -1 : i32} : <>, <i32>
    %56 = shli %45, %54 {handshake.bb = 6 : ui32, handshake.name = "shli0"} : <i32>
    %57 = addi %45, %56 {handshake.bb = 6 : ui32, handshake.name = "addi13"} : <i32>
    %58 = shli %45, %54 {handshake.bb = 6 : ui32, handshake.name = "shli1"} : <i32>
    %59 = addi %45, %58 {handshake.bb = 6 : ui32, handshake.name = "addi14"} : <i32>
    %60 = br %55 {handshake.bb = 6 : ui32, handshake.name = "br19"} : <i32>
    %61 = br %46 {handshake.bb = 6 : ui32, handshake.name = "br20"} : <i32>
    %62 = br %47 {handshake.bb = 6 : ui32, handshake.name = "br21"} : <i32>
    %63 = br %48 {handshake.bb = 6 : ui32, handshake.name = "br22"} : <i32>
    %64 = br %49 {handshake.bb = 6 : ui32, handshake.name = "br23"} : <i32>
    %65 = br %50 {handshake.bb = 6 : ui32, handshake.name = "br24"} : <i32>
    %66 = br %51 {handshake.bb = 6 : ui32, handshake.name = "br25"} : <i32>
    %67 = br %52 {handshake.bb = 6 : ui32, handshake.name = "br26"} : <i32>
    %68 = br %45 {handshake.bb = 6 : ui32, handshake.name = "br27"} : <i32>
    %69 = br %57 {handshake.bb = 6 : ui32, handshake.name = "br28"} : <i32>
    %70 = br %59 {handshake.bb = 6 : ui32, handshake.name = "br29"} : <i32>
    %71 = br %result_37 {handshake.bb = 6 : ui32, handshake.name = "br30"} : <>
    %72 = mux %index_40 [%60, %trueResult_45] {handshake.bb = 7 : ui32, handshake.name = "mux16"} : <i1>, [<i32>, <i32>] to <i32>
    %73 = mux %index_40 [%61, %trueResult_47] {handshake.bb = 7 : ui32, handshake.name = "mux17"} : <i1>, [<i32>, <i32>] to <i32>
    %74 = mux %index_40 [%62, %trueResult_49] {handshake.bb = 7 : ui32, handshake.name = "mux18"} : <i1>, [<i32>, <i32>] to <i32>
    %75 = mux %index_40 [%63, %trueResult_51] {handshake.bb = 7 : ui32, handshake.name = "mux19"} : <i1>, [<i32>, <i32>] to <i32>
    %76 = mux %index_40 [%64, %trueResult_53] {handshake.bb = 7 : ui32, handshake.name = "mux20"} : <i1>, [<i32>, <i32>] to <i32>
    %77 = mux %index_40 [%65, %trueResult_55] {handshake.bb = 7 : ui32, handshake.name = "mux21"} : <i1>, [<i32>, <i32>] to <i32>
    %78 = mux %index_40 [%66, %trueResult_57] {handshake.bb = 7 : ui32, handshake.name = "mux22"} : <i1>, [<i32>, <i32>] to <i32>
    %79 = mux %index_40 [%67, %trueResult_59] {handshake.bb = 7 : ui32, handshake.name = "mux23"} : <i1>, [<i32>, <i32>] to <i32>
    %80 = mux %index_40 [%68, %trueResult_61] {handshake.bb = 7 : ui32, handshake.name = "mux24"} : <i1>, [<i32>, <i32>] to <i32>
    %81 = mux %index_40 [%69, %trueResult_63] {handshake.bb = 7 : ui32, handshake.name = "mux25"} : <i1>, [<i32>, <i32>] to <i32>
    %82 = mux %index_40 [%70, %trueResult_65] {handshake.bb = 7 : ui32, handshake.name = "mux26"} : <i1>, [<i32>, <i32>] to <i32>
    %result_39, %index_40 = control_merge [%71, %trueResult_67]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>, <>] to <>, <i1>
    %83 = source {handshake.bb = 7 : ui32, handshake.name = "source4"} : <>
    %84 = constant %83 {handshake.bb = 7 : ui32, handshake.name = "constant17", value = 2 : i32} : <>, <i32>
    %85 = source {handshake.bb = 7 : ui32, handshake.name = "source5"} : <>
    %86 = constant %85 {handshake.bb = 7 : ui32, handshake.name = "constant18", value = 1 : i32} : <>, <i32>
    %87 = source {handshake.bb = 7 : ui32, handshake.name = "source6"} : <>
    %88 = constant %87 {handshake.bb = 7 : ui32, handshake.name = "constant19", value = 4 : i32} : <>, <i32>
    %89 = addi %81, %72 {handshake.bb = 7 : ui32, handshake.name = "addi0"} : <i32>
    %90 = addi %89, %88 {handshake.bb = 7 : ui32, handshake.name = "addi1"} : <i32>
    %91 = trunci %90 {handshake.bb = 7 : ui32, handshake.name = "index_cast2"} : <i32> to <i32>
    %addressResult_41, %dataResult_42 = load[%91] %outputs {handshake.bb = 7 : ui32, handshake.name = "load2"} : <i32>, <i32>, <i32>, <i32>
    %92 = muli %78, %dataResult_42 {handshake.bb = 7 : ui32, handshake.name = "muli2"} : <i32>
    %93 = addi %73, %92 {handshake.bb = 7 : ui32, handshake.name = "addi2"} : <i32>
    %94 = addi %82, %72 {handshake.bb = 7 : ui32, handshake.name = "addi3"} : <i32>
    %95 = addi %94, %88 {handshake.bb = 7 : ui32, handshake.name = "addi4"} : <i32>
    %96 = trunci %95 {handshake.bb = 7 : ui32, handshake.name = "index_cast3"} : <i32> to <i32>
    %addressResult_43, %dataResult_44 = load[%96] %outputs_1 {handshake.bb = 7 : ui32, handshake.name = "load3"} : <i32>, <i32>, <i32>, <i32>
    %97 = muli %79, %dataResult_44 {handshake.bb = 7 : ui32, handshake.name = "muli3"} : <i32>
    %98 = addi %74, %97 {handshake.bb = 7 : ui32, handshake.name = "addi5"} : <i32>
    %99 = addi %72, %86 {handshake.bb = 7 : ui32, handshake.name = "addi6"} : <i32>
    %100 = cmpi slt, %99, %84 {handshake.bb = 7 : ui32, handshake.name = "cmpi3"} : <i32>
    %trueResult_45, %falseResult_46 = cond_br %100, %99 {handshake.bb = 7 : ui32, handshake.name = "cond_br19"} : <i1>, <i32>
    %trueResult_47, %falseResult_48 = cond_br %100, %93 {handshake.bb = 7 : ui32, handshake.name = "cond_br20"} : <i1>, <i32>
    %trueResult_49, %falseResult_50 = cond_br %100, %98 {handshake.bb = 7 : ui32, handshake.name = "cond_br21"} : <i1>, <i32>
    %trueResult_51, %falseResult_52 = cond_br %100, %75 {handshake.bb = 7 : ui32, handshake.name = "cond_br22"} : <i1>, <i32>
    %trueResult_53, %falseResult_54 = cond_br %100, %76 {handshake.bb = 7 : ui32, handshake.name = "cond_br23"} : <i1>, <i32>
    %trueResult_55, %falseResult_56 = cond_br %100, %77 {handshake.bb = 7 : ui32, handshake.name = "cond_br24"} : <i1>, <i32>
    %trueResult_57, %falseResult_58 = cond_br %100, %78 {handshake.bb = 7 : ui32, handshake.name = "cond_br25"} : <i1>, <i32>
    %trueResult_59, %falseResult_60 = cond_br %100, %79 {handshake.bb = 7 : ui32, handshake.name = "cond_br26"} : <i1>, <i32>
    %trueResult_61, %falseResult_62 = cond_br %100, %80 {handshake.bb = 7 : ui32, handshake.name = "cond_br27"} : <i1>, <i32>
    %trueResult_63, %falseResult_64 = cond_br %100, %81 {handshake.bb = 7 : ui32, handshake.name = "cond_br28"} : <i1>, <i32>
    %trueResult_65, %falseResult_66 = cond_br %100, %82 {handshake.bb = 7 : ui32, handshake.name = "cond_br29"} : <i1>, <i32>
    %trueResult_67, %falseResult_68 = cond_br %100, %result_39 {handshake.bb = 7 : ui32, handshake.name = "cond_br30"} : <i1>, <>
    %101 = merge %falseResult_50 {handshake.bb = 8 : ui32, handshake.name = "merge6"} : <i32>
    %102 = merge %falseResult_48 {handshake.bb = 8 : ui32, handshake.name = "merge7"} : <i32>
    %103 = merge %falseResult_52 {handshake.bb = 8 : ui32, handshake.name = "merge8"} : <i32>
    %104 = merge %falseResult_54 {handshake.bb = 8 : ui32, handshake.name = "merge9"} : <i32>
    %105 = merge %falseResult_56 {handshake.bb = 8 : ui32, handshake.name = "merge10"} : <i32>
    %106 = merge %falseResult_58 {handshake.bb = 8 : ui32, handshake.name = "merge11"} : <i32>
    %107 = merge %falseResult_60 {handshake.bb = 8 : ui32, handshake.name = "merge12"} : <i32>
    %108 = merge %falseResult_62 {handshake.bb = 8 : ui32, handshake.name = "merge13"} : <i32>
    %result_69, %index_70 = control_merge [%falseResult_68]  {handshake.bb = 8 : ui32, handshake.name = "control_merge7"} : [<>] to <>, <i1>
    %109 = source {handshake.bb = 8 : ui32, handshake.name = "source7"} : <>
    %110 = constant %109 {handshake.bb = 8 : ui32, handshake.name = "constant20", value = 2 : i32} : <>, <i32>
    %111 = source {handshake.bb = 8 : ui32, handshake.name = "source8"} : <>
    %112 = constant %111 {handshake.bb = 8 : ui32, handshake.name = "constant21", value = 1 : i32} : <>, <i32>
    %113 = addi %108, %112 {handshake.bb = 8 : ui32, handshake.name = "addi7"} : <i32>
    %114 = cmpi slt, %113, %110 {handshake.bb = 8 : ui32, handshake.name = "cmpi4"} : <i32>
    %trueResult_71, %falseResult_72 = cond_br %114, %113 {handshake.bb = 8 : ui32, handshake.name = "cond_br31"} : <i1>, <i32>
    %trueResult_73, %falseResult_74 = cond_br %114, %102 {handshake.bb = 8 : ui32, handshake.name = "cond_br32"} : <i1>, <i32>
    %trueResult_75, %falseResult_76 = cond_br %114, %101 {handshake.bb = 8 : ui32, handshake.name = "cond_br33"} : <i1>, <i32>
    %trueResult_77, %falseResult_78 = cond_br %114, %103 {handshake.bb = 8 : ui32, handshake.name = "cond_br34"} : <i1>, <i32>
    %trueResult_79, %falseResult_80 = cond_br %114, %104 {handshake.bb = 8 : ui32, handshake.name = "cond_br35"} : <i1>, <i32>
    %trueResult_81, %falseResult_82 = cond_br %114, %105 {handshake.bb = 8 : ui32, handshake.name = "cond_br36"} : <i1>, <i32>
    %trueResult_83, %falseResult_84 = cond_br %114, %106 {handshake.bb = 8 : ui32, handshake.name = "cond_br37"} : <i1>, <i32>
    %trueResult_85, %falseResult_86 = cond_br %114, %107 {handshake.bb = 8 : ui32, handshake.name = "cond_br38"} : <i1>, <i32>
    %trueResult_87, %falseResult_88 = cond_br %114, %result_69 {handshake.bb = 8 : ui32, handshake.name = "cond_br39"} : <i1>, <>
    %115 = merge %falseResult_76 {handshake.bb = 9 : ui32, handshake.name = "merge14"} : <i32>
    %116 = merge %falseResult_74 {handshake.bb = 9 : ui32, handshake.name = "merge15"} : <i32>
    %117 = merge %falseResult_78 {handshake.bb = 9 : ui32, handshake.name = "merge16"} : <i32>
    %118 = merge %falseResult_80 {handshake.bb = 9 : ui32, handshake.name = "merge17"} : <i32>
    %119 = merge %falseResult_82 {handshake.bb = 9 : ui32, handshake.name = "merge18"} : <i32>
    %result_89, %index_90 = control_merge [%falseResult_88]  {handshake.bb = 9 : ui32, handshake.name = "control_merge8"} : [<>] to <>, <i1>
    %120 = source {handshake.bb = 9 : ui32, handshake.name = "source9"} : <>
    %121 = constant %120 {handshake.bb = 9 : ui32, handshake.name = "constant22", value = 255 : i32} : <>, <i32>
    %122 = source {handshake.bb = 9 : ui32, handshake.name = "source10"} : <>
    %123 = constant %122 {handshake.bb = 9 : ui32, handshake.name = "constant23", value = 0 : i32} : <>, <i32>
    %124 = cmpi sgt, %115, %121 {handshake.bb = 9 : ui32, handshake.name = "cmpi5"} : <i32>
    %125 = select %124[%121, %115] {handshake.bb = 9 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %126 = cmpi slt, %125, %123 {handshake.bb = 9 : ui32, handshake.name = "cmpi6"} : <i32>
    %127 = select %126[%123, %125] {handshake.bb = 9 : ui32, handshake.name = "select1"} : <i1>, <i32>
    %128 = cmpi sgt, %116, %121 {handshake.bb = 9 : ui32, handshake.name = "cmpi7"} : <i32>
    %129 = select %128[%121, %116] {handshake.bb = 9 : ui32, handshake.name = "select2"} : <i1>, <i32>
    %130 = cmpi slt, %129, %123 {handshake.bb = 9 : ui32, handshake.name = "cmpi8"} : <i32>
    %131 = select %130[%123, %129] {handshake.bb = 9 : ui32, handshake.name = "select3"} : <i1>, <i32>
    %132 = addi %127, %131 {handshake.bb = 9 : ui32, handshake.name = "addi8"} : <i32>
    %133 = addi %118, %132 {handshake.bb = 9 : ui32, handshake.name = "addi9"} : <i32>
    %134 = br %133 {handshake.bb = 9 : ui32, handshake.name = "br31"} : <i32>
    %135 = br %117 {handshake.bb = 9 : ui32, handshake.name = "br32"} : <i32>
    %136 = br %119 {handshake.bb = 9 : ui32, handshake.name = "br33"} : <i32>
    %137 = br %result_89 {handshake.bb = 9 : ui32, handshake.name = "br34"} : <>
    %138 = constant %result_91 {handshake.bb = 10 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %139 = mux %index_92 [%trueResult_15, %trueResult_25, %134] {handshake.bb = 10 : ui32, handshake.name = "mux27"} : <i2>, [<i32>, <i32>, <i32>] to <i32>
    %140 = mux %index_92 [%trueResult_17, %trueResult_27, %135] {handshake.bb = 10 : ui32, handshake.name = "mux28"} : <i2>, [<i32>, <i32>, <i32>] to <i32>
    %141 = mux %index_92 [%trueResult_19, %trueResult_29, %136] {handshake.bb = 10 : ui32, handshake.name = "mux29"} : <i2>, [<i32>, <i32>, <i32>] to <i32>
    %result_91, %index_92 = control_merge [%trueResult_21, %trueResult_31, %137]  {handshake.bb = 10 : ui32, handshake.name = "control_merge9"} : [<>, <>, <>] to <>, <i2>
    %142 = source {handshake.bb = 10 : ui32, handshake.name = "source11"} : <>
    %143 = constant %142 {handshake.bb = 10 : ui32, handshake.name = "constant24", value = 15 : i32} : <>, <i32>
    %144 = source {handshake.bb = 10 : ui32, handshake.name = "source12"} : <>
    %145 = constant %144 {handshake.bb = 10 : ui32, handshake.name = "constant25", value = 255 : i32} : <>, <i32>
    %146 = source {handshake.bb = 10 : ui32, handshake.name = "source13"} : <>
    %147 = constant %146 {handshake.bb = 10 : ui32, handshake.name = "constant26", value = 1 : i32} : <>, <i32>
    %148 = andi %139, %145 {handshake.bb = 10 : ui32, handshake.name = "andi0"} : <i32>
    %149 = xori %148, %145 {handshake.bb = 10 : ui32, handshake.name = "xori0"} : <i32>
    %150 = addi %141, %140 {handshake.bb = 10 : ui32, handshake.name = "addi10"} : <i32>
    %151 = extui %150 {handshake.bb = 10 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %152 = trunci %151 {handshake.bb = 10 : ui32, handshake.name = "index_cast4"} : <i64> to <i32>
    %addressResult_93, %dataResult_94 = store[%152] %149 {handshake.bb = 10 : ui32, handshake.name = "store4"} : <i32>, <i32>, <i32>, <i32>
    %153 = addi %141, %147 {handshake.bb = 10 : ui32, handshake.name = "addi11"} : <i32>
    %154 = cmpi ult, %153, %143 {handshake.bb = 10 : ui32, handshake.name = "cmpi9"} : <i32>
    %trueResult_95, %falseResult_96 = cond_br %154, %139 {handshake.bb = 10 : ui32, handshake.name = "cond_br40"} : <i1>, <i32>
    %trueResult_97, %falseResult_98 = cond_br %154, %153 {handshake.bb = 10 : ui32, handshake.name = "cond_br41"} : <i1>, <i32>
    %trueResult_99, %falseResult_100 = cond_br %154, %140 {handshake.bb = 10 : ui32, handshake.name = "cond_br42"} : <i1>, <i32>
    %trueResult_101, %falseResult_102 = cond_br %154, %result_91 {handshake.bb = 10 : ui32, handshake.name = "cond_br43"} : <i1>, <>
    %155 = merge %falseResult_96 {handshake.bb = 11 : ui32, handshake.name = "merge19"} : <i32>
    %156 = merge %falseResult_100 {handshake.bb = 11 : ui32, handshake.name = "merge20"} : <i32>
    %result_103, %index_104 = control_merge [%falseResult_102]  {handshake.bb = 11 : ui32, handshake.name = "control_merge10"} : [<>] to <>, <i1>
    %157 = source {handshake.bb = 11 : ui32, handshake.name = "source14"} : <>
    %158 = constant %157 {handshake.bb = 11 : ui32, handshake.name = "constant27", value = 15 : i32} : <>, <i32>
    %159 = source {handshake.bb = 11 : ui32, handshake.name = "source15"} : <>
    %160 = constant %159 {handshake.bb = 11 : ui32, handshake.name = "constant28", value = 1 : i32} : <>, <i32>
    %161 = addi %156, %160 {handshake.bb = 11 : ui32, handshake.name = "addi12"} : <i32>
    %162 = cmpi ult, %161, %158 {handshake.bb = 11 : ui32, handshake.name = "cmpi10"} : <i32>
    %trueResult_105, %falseResult_106 = cond_br %162, %155 {handshake.bb = 11 : ui32, handshake.name = "cond_br44"} : <i1>, <i32>
    %trueResult_107, %falseResult_108 = cond_br %162, %161 {handshake.bb = 11 : ui32, handshake.name = "cond_br45"} : <i1>, <i32>
    %trueResult_109, %falseResult_110 = cond_br %162, %result_103 {handshake.bb = 11 : ui32, handshake.name = "cond_br46"} : <i1>, <>
    %163 = merge %falseResult_106 {handshake.bb = 12 : ui32, handshake.name = "merge21"} : <i32>
    %result_111, %index_112 = control_merge [%falseResult_110]  {handshake.bb = 12 : ui32, handshake.name = "control_merge11"} : [<>] to <>, <i1>
    end {handshake.bb = 12 : ui32, handshake.name = "end0"} %163, %memEnd_4, %memEnd_2, %memEnd_0, %memEnd, %arg8 : <i32>, <>, <>, <>, <>, <>
  }
}

