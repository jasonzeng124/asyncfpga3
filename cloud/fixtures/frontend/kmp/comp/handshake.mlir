module {
  handshake.func @kmp(%arg0: memref<4xi8>, %arg1: memref<1000xi8>, %arg2: memref<4xi32>, %arg3: !handshake.control<>, %arg4: !handshake.control<>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["pattern", "input", "kmpNext", "pattern_start", "input_start", "kmpNext_start", "start"], resNames = ["out0", "pattern_end", "input_end", "kmpNext_end", "end"]} {
    %0:4 = lsq[%arg2 : memref<4xi32>] (%arg5, %arg6, %addressResult, %dataResult, %result_22, %addressResult_24, %result_34, %addressResult_38, %dataResult_39, %result_76, %addressResult_78, %result_102, %addressResult_104, %result_116)  {groupSizes = [1 : i32, 1 : i32, 1 : i32, 1 : i32, 1 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>, !handshake.channel<i32>, !handshake.control<>) -> (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.control<>)
    %outputs, %memEnd = mem_controller[%arg1 : memref<1000xi8>] %arg4 (%addressResult_50) %result_116 {connectedBlocks = [5 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>) -> !handshake.channel<i8>
    %outputs_0:5, %memEnd_1 = mem_controller[%arg0 : memref<4xi8>] %arg3 (%addressResult_2, %addressResult_12, %addressResult_36, %addressResult_64, %addressResult_92) %result_116 {connectedBlocks = [1 : i32, 2 : i32, 4 : i32, 6 : i32, 8 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<i8>, !handshake.channel<i8>, !handshake.channel<i8>, !handshake.channel<i8>, !handshake.channel<i8>)
    %1 = constant %arg6 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = constant %arg6 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 1 : i32} : <>, <i32>
    %3 = constant %arg6 {handshake.bb = 0 : ui32, handshake.name = "constant6", value = 0 : i32} : <>, <i32>
    %addressResult, %dataResult = store[%3] %1 {handshake.bb = 0 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load10", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store0"} : <i32>, <i32>, <i32>, <i32>
    %4 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %5 = br %2 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <i32>
    %6 = br %arg6 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <>
    %7 = mux %index [%4, %trueResult_40] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %8 = mux %index [%5, %trueResult_42] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%6, %trueResult_44]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %9 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %10 = constant %9 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 0 : i32} : <>, <i32>
    %11 = extui %8 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %12 = trunci %11 {handshake.bb = 1 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult_2, %dataResult_3 = load[%12] %outputs_0#0 {handshake.bb = 1 : ui32, handshake.name = "load1"} : <i32>, <i8>, <i32>, <i8>
    %13 = cmpi sgt, %7, %10 {handshake.bb = 1 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %13, %7 {handshake.bb = 1 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %13, %8 {handshake.bb = 1 : ui32, handshake.name = "cond_br10"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %13, %dataResult_3 {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <i8>
    %trueResult_8, %falseResult_9 = cond_br %13, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br12"} : <i1>, <>
    %14 = mux %index_11 [%trueResult, %trueResult_26] {handshake.bb = 2 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %15 = mux %index_11 [%trueResult_4, %trueResult_28] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %16 = mux %index_11 [%trueResult_6, %trueResult_30] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i8>, <i8>] to <i8>
    %result_10, %index_11 = control_merge [%trueResult_8, %trueResult_32]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %17 = trunci %14 {handshake.bb = 2 : ui32, handshake.name = "index_cast1"} : <i32> to <i32>
    %addressResult_12, %dataResult_13 = load[%17] %outputs_0#1 {handshake.bb = 2 : ui32, handshake.name = "load2"} : <i32>, <i8>, <i32>, <i8>
    %18 = cmpi eq, %dataResult_13, %16 {handshake.bb = 2 : ui32, handshake.name = "cmpi1"} : <i8>
    %trueResult_14, %falseResult_15 = cond_br %18, %14 {handshake.bb = 2 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %18, %15 {handshake.bb = 2 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %18, %16 {handshake.bb = 2 : ui32, handshake.name = "cond_br15"} : <i1>, <i8>
    %trueResult_20, %falseResult_21 = cond_br %18, %result_10 {handshake.bb = 2 : ui32, handshake.name = "cond_br16"} : <i1>, <>
    %19 = merge %falseResult_17 {handshake.bb = 3 : ui32, handshake.name = "merge0"} : <i32>
    %20 = merge %falseResult_19 {handshake.bb = 3 : ui32, handshake.name = "merge1"} : <i8>
    %result_22, %index_23 = control_merge [%falseResult_21]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>] to <>, <i1>
    %21 = source {handshake.bb = 3 : ui32, handshake.name = "source1"} : <>
    %22 = constant %21 {handshake.bb = 3 : ui32, handshake.name = "constant8", value = 0 : i32} : <>, <i32>
    %23 = extui %19 {handshake.bb = 3 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %24 = trunci %23 {handshake.bb = 3 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_24, %dataResult_25 = load[%24] %0#0 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load3"} : <i32>, <i32>, <i32>, <i32>
    %25 = cmpi sgt, %dataResult_25, %22 {handshake.bb = 3 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_26, %falseResult_27 = cond_br %25, %dataResult_25 {handshake.bb = 3 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    %trueResult_28, %falseResult_29 = cond_br %25, %19 {handshake.bb = 3 : ui32, handshake.name = "cond_br18"} : <i1>, <i32>
    %trueResult_30, %falseResult_31 = cond_br %25, %20 {handshake.bb = 3 : ui32, handshake.name = "cond_br19"} : <i1>, <i8>
    %trueResult_32, %falseResult_33 = cond_br %25, %result_22 {handshake.bb = 3 : ui32, handshake.name = "cond_br20"} : <i1>, <>
    %26 = mux %index_35 [%falseResult, %trueResult_14, %falseResult_27] {handshake.bb = 4 : ui32, handshake.name = "mux5"} : <i2>, [<i32>, <i32>, <i32>] to <i32>
    %27 = mux %index_35 [%falseResult_5, %trueResult_16, %falseResult_29] {handshake.bb = 4 : ui32, handshake.name = "mux6"} : <i2>, [<i32>, <i32>, <i32>] to <i32>
    %28 = mux %index_35 [%falseResult_7, %trueResult_18, %falseResult_31] {handshake.bb = 4 : ui32, handshake.name = "mux7"} : <i2>, [<i8>, <i8>, <i8>] to <i8>
    %result_34, %index_35 = control_merge [%falseResult_9, %trueResult_20, %falseResult_33]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>, <>] to <>, <i2>
    %29 = source {handshake.bb = 4 : ui32, handshake.name = "source2"} : <>
    %30 = constant %29 {handshake.bb = 4 : ui32, handshake.name = "constant9", value = 4 : i32} : <>, <i32>
    %31 = source {handshake.bb = 4 : ui32, handshake.name = "source3"} : <>
    %32 = constant %31 {handshake.bb = 4 : ui32, handshake.name = "constant10", value = 1 : i32} : <>, <i32>
    %33 = constant %result_34 {handshake.bb = 4 : ui32, handshake.name = "constant11", value = 0 : i32} : <>, <i32>
    %34 = trunci %26 {handshake.bb = 4 : ui32, handshake.name = "index_cast3"} : <i32> to <i32>
    %addressResult_36, %dataResult_37 = load[%34] %outputs_0#2 {handshake.bb = 4 : ui32, handshake.name = "load4"} : <i32>, <i8>, <i32>, <i8>
    %35 = cmpi eq, %dataResult_37, %28 {handshake.bb = 4 : ui32, handshake.name = "cmpi3"} : <i8>
    %36 = addi %26, %32 {handshake.bb = 4 : ui32, handshake.name = "addi0"} : <i32>
    %37 = select %35[%36, %26] {handshake.bb = 4 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %38 = extui %27 {handshake.bb = 4 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %39 = trunci %38 {handshake.bb = 4 : ui32, handshake.name = "index_cast4"} : <i64> to <i32>
    %addressResult_38, %dataResult_39 = store[%39] %37 {handshake.bb = 4 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load8", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load10", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : <i32>, <i32>, <i32>, <i32>
    %40 = addi %27, %32 {handshake.bb = 4 : ui32, handshake.name = "addi1"} : <i32>
    %41 = cmpi ult, %40, %30 {handshake.bb = 4 : ui32, handshake.name = "cmpi4"} : <i32>
    %trueResult_40, %falseResult_41 = cond_br %41, %37 {handshake.bb = 4 : ui32, handshake.name = "cond_br21"} : <i1>, <i32>
    %trueResult_42, %falseResult_43 = cond_br %41, %40 {handshake.bb = 4 : ui32, handshake.name = "cond_br22"} : <i1>, <i32>
    %trueResult_44, %falseResult_45 = cond_br %41, %result_34 {handshake.bb = 4 : ui32, handshake.name = "cond_br23"} : <i1>, <>
    %trueResult_46, %falseResult_47 = cond_br %41, %33 {handshake.bb = 4 : ui32, handshake.name = "cond_br24"} : <i1>, <i32>
    %42 = mux %index_49 [%falseResult_47, %trueResult_108] {handshake.bb = 5 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %43 = mux %index_49 [%falseResult_47, %trueResult_110] {handshake.bb = 5 : ui32, handshake.name = "mux9"} : <i1>, [<i32>, <i32>] to <i32>
    %44 = mux %index_49 [%falseResult_47, %trueResult_112] {handshake.bb = 5 : ui32, handshake.name = "mux10"} : <i1>, [<i32>, <i32>] to <i32>
    %result_48, %index_49 = control_merge [%falseResult_45, %trueResult_114]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    %45 = source {handshake.bb = 5 : ui32, handshake.name = "source4"} : <>
    %46 = constant %45 {handshake.bb = 5 : ui32, handshake.name = "constant12", value = 0 : i32} : <>, <i32>
    %47 = extui %44 {handshake.bb = 5 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %48 = trunci %47 {handshake.bb = 5 : ui32, handshake.name = "index_cast5"} : <i64> to <i32>
    %addressResult_50, %dataResult_51 = load[%48] %outputs {handshake.bb = 5 : ui32, handshake.name = "load6"} : <i32>, <i8>, <i32>, <i8>
    %49 = cmpi sgt, %43, %46 {handshake.bb = 5 : ui32, handshake.name = "cmpi5"} : <i32>
    %trueResult_52, %falseResult_53 = cond_br %49, %43 {handshake.bb = 5 : ui32, handshake.name = "cond_br25"} : <i1>, <i32>
    %trueResult_54, %falseResult_55 = cond_br %49, %42 {handshake.bb = 5 : ui32, handshake.name = "cond_br26"} : <i1>, <i32>
    %trueResult_56, %falseResult_57 = cond_br %49, %44 {handshake.bb = 5 : ui32, handshake.name = "cond_br27"} : <i1>, <i32>
    %trueResult_58, %falseResult_59 = cond_br %49, %dataResult_51 {handshake.bb = 5 : ui32, handshake.name = "cond_br28"} : <i1>, <i8>
    %trueResult_60, %falseResult_61 = cond_br %49, %result_48 {handshake.bb = 5 : ui32, handshake.name = "cond_br29"} : <i1>, <>
    %50 = mux %index_63 [%trueResult_52, %trueResult_80] {handshake.bb = 6 : ui32, handshake.name = "mux11"} : <i1>, [<i32>, <i32>] to <i32>
    %51 = mux %index_63 [%trueResult_54, %trueResult_82] {handshake.bb = 6 : ui32, handshake.name = "mux12"} : <i1>, [<i32>, <i32>] to <i32>
    %52 = mux %index_63 [%trueResult_56, %trueResult_84] {handshake.bb = 6 : ui32, handshake.name = "mux13"} : <i1>, [<i32>, <i32>] to <i32>
    %53 = mux %index_63 [%trueResult_58, %trueResult_86] {handshake.bb = 6 : ui32, handshake.name = "mux14"} : <i1>, [<i8>, <i8>] to <i8>
    %result_62, %index_63 = control_merge [%trueResult_60, %trueResult_88]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>, <>] to <>, <i1>
    %54 = trunci %50 {handshake.bb = 6 : ui32, handshake.name = "index_cast6"} : <i32> to <i32>
    %addressResult_64, %dataResult_65 = load[%54] %outputs_0#3 {handshake.bb = 6 : ui32, handshake.name = "load7"} : <i32>, <i8>, <i32>, <i8>
    %55 = cmpi eq, %dataResult_65, %53 {handshake.bb = 6 : ui32, handshake.name = "cmpi6"} : <i8>
    %trueResult_66, %falseResult_67 = cond_br %55, %50 {handshake.bb = 6 : ui32, handshake.name = "cond_br30"} : <i1>, <i32>
    %trueResult_68, %falseResult_69 = cond_br %55, %51 {handshake.bb = 6 : ui32, handshake.name = "cond_br31"} : <i1>, <i32>
    %trueResult_70, %falseResult_71 = cond_br %55, %52 {handshake.bb = 6 : ui32, handshake.name = "cond_br32"} : <i1>, <i32>
    %trueResult_72, %falseResult_73 = cond_br %55, %53 {handshake.bb = 6 : ui32, handshake.name = "cond_br33"} : <i1>, <i8>
    %trueResult_74, %falseResult_75 = cond_br %55, %result_62 {handshake.bb = 6 : ui32, handshake.name = "cond_br34"} : <i1>, <>
    %56 = merge %falseResult_69 {handshake.bb = 7 : ui32, handshake.name = "merge2"} : <i32>
    %57 = merge %falseResult_71 {handshake.bb = 7 : ui32, handshake.name = "merge3"} : <i32>
    %58 = merge %falseResult_73 {handshake.bb = 7 : ui32, handshake.name = "merge4"} : <i8>
    %59 = merge %falseResult_67 {handshake.bb = 7 : ui32, handshake.name = "merge5"} : <i32>
    %result_76, %index_77 = control_merge [%falseResult_75]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>] to <>, <i1>
    %60 = source {handshake.bb = 7 : ui32, handshake.name = "source5"} : <>
    %61 = constant %60 {handshake.bb = 7 : ui32, handshake.name = "constant13", value = 0 : i32} : <>, <i32>
    %62 = trunci %59 {handshake.bb = 7 : ui32, handshake.name = "index_cast7"} : <i32> to <i32>
    %addressResult_78, %dataResult_79 = load[%62] %0#1 {handshake.bb = 7 : ui32, handshake.name = "load8"} : <i32>, <i32>, <i32>, <i32>
    %63 = cmpi sgt, %dataResult_79, %61 {handshake.bb = 7 : ui32, handshake.name = "cmpi7"} : <i32>
    %trueResult_80, %falseResult_81 = cond_br %63, %dataResult_79 {handshake.bb = 7 : ui32, handshake.name = "cond_br35"} : <i1>, <i32>
    %trueResult_82, %falseResult_83 = cond_br %63, %56 {handshake.bb = 7 : ui32, handshake.name = "cond_br36"} : <i1>, <i32>
    %trueResult_84, %falseResult_85 = cond_br %63, %57 {handshake.bb = 7 : ui32, handshake.name = "cond_br37"} : <i1>, <i32>
    %trueResult_86, %falseResult_87 = cond_br %63, %58 {handshake.bb = 7 : ui32, handshake.name = "cond_br38"} : <i1>, <i8>
    %trueResult_88, %falseResult_89 = cond_br %63, %result_76 {handshake.bb = 7 : ui32, handshake.name = "cond_br39"} : <i1>, <>
    %64 = mux %index_91 [%falseResult_53, %trueResult_66, %falseResult_81] {handshake.bb = 8 : ui32, handshake.name = "mux15"} : <i2>, [<i32>, <i32>, <i32>] to <i32>
    %65 = mux %index_91 [%falseResult_55, %trueResult_68, %falseResult_83] {handshake.bb = 8 : ui32, handshake.name = "mux16"} : <i2>, [<i32>, <i32>, <i32>] to <i32>
    %66 = mux %index_91 [%falseResult_57, %trueResult_70, %falseResult_85] {handshake.bb = 8 : ui32, handshake.name = "mux17"} : <i2>, [<i32>, <i32>, <i32>] to <i32>
    %67 = mux %index_91 [%falseResult_59, %trueResult_72, %falseResult_87] {handshake.bb = 8 : ui32, handshake.name = "mux18"} : <i2>, [<i8>, <i8>, <i8>] to <i8>
    %result_90, %index_91 = control_merge [%falseResult_61, %trueResult_74, %falseResult_89]  {handshake.bb = 8 : ui32, handshake.name = "control_merge7"} : [<>, <>, <>] to <>, <i2>
    %68 = source {handshake.bb = 8 : ui32, handshake.name = "source6"} : <>
    %69 = constant %68 {handshake.bb = 8 : ui32, handshake.name = "constant14", value = 3 : i32} : <>, <i32>
    %70 = source {handshake.bb = 8 : ui32, handshake.name = "source7"} : <>
    %71 = constant %70 {handshake.bb = 8 : ui32, handshake.name = "constant15", value = 1 : i32} : <>, <i32>
    %72 = trunci %64 {handshake.bb = 8 : ui32, handshake.name = "index_cast8"} : <i32> to <i32>
    %addressResult_92, %dataResult_93 = load[%72] %outputs_0#4 {handshake.bb = 8 : ui32, handshake.name = "load9"} : <i32>, <i8>, <i32>, <i8>
    %73 = cmpi eq, %dataResult_93, %67 {handshake.bb = 8 : ui32, handshake.name = "cmpi8"} : <i8>
    %74 = addi %64, %71 {handshake.bb = 8 : ui32, handshake.name = "addi2"} : <i32>
    %75 = select %73[%74, %64] {handshake.bb = 8 : ui32, handshake.name = "select1"} : <i1>, <i32>
    %76 = cmpi sgt, %75, %69 {handshake.bb = 8 : ui32, handshake.name = "cmpi9"} : <i32>
    %trueResult_94, %falseResult_95 = cond_br %76, %65 {handshake.bb = 8 : ui32, handshake.name = "cond_br40"} : <i1>, <i32>
    %trueResult_96, %falseResult_97 = cond_br %76, %66 {handshake.bb = 8 : ui32, handshake.name = "cond_br41"} : <i1>, <i32>
    %trueResult_98, %falseResult_99 = cond_br %76, %75 {handshake.bb = 8 : ui32, handshake.name = "cond_br42"} : <i1>, <i32>
    %trueResult_100, %falseResult_101 = cond_br %76, %result_90 {handshake.bb = 8 : ui32, handshake.name = "cond_br43"} : <i1>, <>
    %77 = merge %trueResult_94 {handshake.bb = 9 : ui32, handshake.name = "merge6"} : <i32>
    %78 = merge %trueResult_96 {handshake.bb = 9 : ui32, handshake.name = "merge7"} : <i32>
    %79 = merge %trueResult_98 {handshake.bb = 9 : ui32, handshake.name = "merge8"} : <i32>
    %result_102, %index_103 = control_merge [%trueResult_100]  {handshake.bb = 9 : ui32, handshake.name = "control_merge8"} : [<>] to <>, <i1>
    %80 = source {handshake.bb = 9 : ui32, handshake.name = "source8"} : <>
    %81 = constant %80 {handshake.bb = 9 : ui32, handshake.name = "constant16", value = -1 : i32} : <>, <i32>
    %82 = source {handshake.bb = 9 : ui32, handshake.name = "source9"} : <>
    %83 = constant %82 {handshake.bb = 9 : ui32, handshake.name = "constant17", value = 1 : i32} : <>, <i32>
    %84 = addi %77, %83 {handshake.bb = 9 : ui32, handshake.name = "addi3"} : <i32>
    %85 = addi %79, %81 {handshake.bb = 9 : ui32, handshake.name = "addi4"} : <i32>
    %86 = trunci %85 {handshake.bb = 9 : ui32, handshake.name = "index_cast9"} : <i32> to <i32>
    %addressResult_104, %dataResult_105 = load[%86] %0#2 {handshake.bb = 9 : ui32, handshake.name = "load10"} : <i32>, <i32>, <i32>, <i32>
    %87 = br %dataResult_105 {handshake.bb = 9 : ui32, handshake.name = "br5"} : <i32>
    %88 = br %84 {handshake.bb = 9 : ui32, handshake.name = "br6"} : <i32>
    %89 = br %78 {handshake.bb = 9 : ui32, handshake.name = "br7"} : <i32>
    %90 = br %result_102 {handshake.bb = 9 : ui32, handshake.name = "br8"} : <>
    %91 = mux %index_107 [%falseResult_99, %87] {handshake.bb = 10 : ui32, handshake.name = "mux19"} : <i1>, [<i32>, <i32>] to <i32>
    %92 = mux %index_107 [%falseResult_95, %88] {handshake.bb = 10 : ui32, handshake.name = "mux20"} : <i1>, [<i32>, <i32>] to <i32>
    %93 = mux %index_107 [%falseResult_97, %89] {handshake.bb = 10 : ui32, handshake.name = "mux21"} : <i1>, [<i32>, <i32>] to <i32>
    %result_106, %index_107 = control_merge [%falseResult_101, %90]  {handshake.bb = 10 : ui32, handshake.name = "control_merge9"} : [<>, <>] to <>, <i1>
    %94 = source {handshake.bb = 10 : ui32, handshake.name = "source10"} : <>
    %95 = constant %94 {handshake.bb = 10 : ui32, handshake.name = "constant18", value = 1000 : i32} : <>, <i32>
    %96 = source {handshake.bb = 10 : ui32, handshake.name = "source11"} : <>
    %97 = constant %96 {handshake.bb = 10 : ui32, handshake.name = "constant19", value = 1 : i32} : <>, <i32>
    %98 = addi %93, %97 {handshake.bb = 10 : ui32, handshake.name = "addi5"} : <i32>
    %99 = cmpi ult, %98, %95 {handshake.bb = 10 : ui32, handshake.name = "cmpi10"} : <i32>
    %trueResult_108, %falseResult_109 = cond_br %99, %92 {handshake.bb = 10 : ui32, handshake.name = "cond_br44"} : <i1>, <i32>
    %trueResult_110, %falseResult_111 = cond_br %99, %91 {handshake.bb = 10 : ui32, handshake.name = "cond_br45"} : <i1>, <i32>
    %trueResult_112, %falseResult_113 = cond_br %99, %98 {handshake.bb = 10 : ui32, handshake.name = "cond_br46"} : <i1>, <i32>
    %trueResult_114, %falseResult_115 = cond_br %99, %result_106 {handshake.bb = 10 : ui32, handshake.name = "cond_br47"} : <i1>, <>
    %100 = merge %falseResult_109 {handshake.bb = 11 : ui32, handshake.name = "merge9"} : <i32>
    %result_116, %index_117 = control_merge [%falseResult_115]  {handshake.bb = 11 : ui32, handshake.name = "control_merge10"} : [<>] to <>, <i1>
    end {handshake.bb = 11 : ui32, handshake.name = "end0"} %100, %memEnd_1, %memEnd, %0#3, %arg6 : <i32>, <>, <>, <>, <>
  }
}

