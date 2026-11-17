module {
  handshake.func @symm_float(%arg0: memref<900xf32>, %arg1: memref<900xf32>, %arg2: memref<900xf32>, %arg3: !handshake.channel<f32>, %arg4: !handshake.channel<f32>, %arg5: !handshake.control<>, %arg6: !handshake.control<>, %arg7: !handshake.control<>, %arg8: !handshake.control<>, ...) -> (!handshake.control<>, !handshake.control<>, !handshake.control<>, !handshake.control<>) attributes {argNames = ["A", "B", "C", "alpha", "beta", "A_start", "B_start", "C_start", "start"], resNames = ["A_end", "B_end", "C_end", "end"]} {
    %0:3 = lsq[%arg2 : memref<900xf32>] (%arg7, %result_26, %addressResult_30, %addressResult_32, %dataResult_33, %result_62, %addressResult_64, %addressResult_70, %dataResult_71, %result_100)  {groupSizes = [2 : i32, 2 : i32], handshake.name = "lsq0"} : (!handshake.control<>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.control<>, !handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<f32>, !handshake.control<>) -> (!handshake.channel<f32>, !handshake.channel<f32>, !handshake.control<>)
    %outputs:3, %memEnd = mem_controller[%arg1 : memref<900xf32>] %arg6 (%addressResult_28, %addressResult_34, %addressResult_68) %result_100 {connectedBlocks = [3 : i32, 4 : i32], handshake.name = "mem_controller0"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<f32>, !handshake.channel<f32>, !handshake.channel<f32>)
    %outputs_0:3, %memEnd_1 = mem_controller[%arg0 : memref<900xf32>] %arg5 (%addressResult, %addressResult_36, %addressResult_66) %result_100 {connectedBlocks = [3 : i32, 4 : i32], handshake.name = "mem_controller1"} :    (!handshake.channel<i32>, !handshake.channel<i32>, !handshake.channel<i32>) -> (!handshake.channel<f32>, !handshake.channel<f32>, !handshake.channel<f32>)
    %1 = constant %arg8 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = br %1 {handshake.bb = 0 : ui32, handshake.name = "br2"} : <i32>
    %3 = br %arg3 {handshake.bb = 0 : ui32, handshake.name = "br3"} : <f32>
    %4 = br %arg4 {handshake.bb = 0 : ui32, handshake.name = "br4"} : <f32>
    %5 = br %arg8 {handshake.bb = 0 : ui32, handshake.name = "br5"} : <>
    %6 = mux %index [%2, %trueResult_92] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %7 = mux %index [%3, %trueResult_94] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<f32>, <f32>] to <f32>
    %8 = mux %index [%4, %trueResult_96] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<f32>, <f32>] to <f32>
    %result, %index = control_merge [%5, %trueResult_98]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %9 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant11", value = 0 : i32} : <>, <i32>
    %10 = source {handshake.bb = 1 : ui32, handshake.name = "source0"} : <>
    %11 = constant %10 {handshake.bb = 1 : ui32, handshake.name = "constant12", value = 4 : i64} : <>, <i64>
    %12 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %13 = constant %12 {handshake.bb = 1 : ui32, handshake.name = "constant13", value = 3 : i64} : <>, <i64>
    %14 = source {handshake.bb = 1 : ui32, handshake.name = "source2"} : <>
    %15 = constant %14 {handshake.bb = 1 : ui32, handshake.name = "constant14", value = 2 : i64} : <>, <i64>
    %16 = source {handshake.bb = 1 : ui32, handshake.name = "source3"} : <>
    %17 = constant %16 {handshake.bb = 1 : ui32, handshake.name = "constant15", value = 1 : i64} : <>, <i64>
    %18 = extui %6 {handshake.bb = 1 : ui32, handshake.name = "extui0"} : <i32> to <i64>
    %19 = extui %6 {handshake.bb = 1 : ui32, handshake.name = "extui1"} : <i32> to <i64>
    %20 = extui %6 {handshake.bb = 1 : ui32, handshake.name = "extui2"} : <i32> to <i64>
    %21 = shli %19, %17 {handshake.bb = 1 : ui32, handshake.name = "shli0"} : <i64>
    %22 = shli %19, %15 {handshake.bb = 1 : ui32, handshake.name = "shli1"} : <i64>
    %23 = addi %21, %22 {handshake.bb = 1 : ui32, handshake.name = "addi13"} : <i64>
    %24 = shli %19, %13 {handshake.bb = 1 : ui32, handshake.name = "shli2"} : <i64>
    %25 = shli %19, %11 {handshake.bb = 1 : ui32, handshake.name = "shli3"} : <i64>
    %26 = addi %24, %25 {handshake.bb = 1 : ui32, handshake.name = "addi14"} : <i64>
    %27 = addi %23, %26 {handshake.bb = 1 : ui32, handshake.name = "addi15"} : <i64>
    %28 = addi %27, %20 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i64>
    %29 = extui %6 {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i32> to <i64>
    %30 = extui %6 {handshake.bb = 1 : ui32, handshake.name = "extui4"} : <i32> to <i64>
    %31 = br %9 {handshake.bb = 1 : ui32, handshake.name = "br6"} : <i32>
    %32 = br %7 {handshake.bb = 1 : ui32, handshake.name = "br7"} : <f32>
    %33 = br %8 {handshake.bb = 1 : ui32, handshake.name = "br8"} : <f32>
    %34 = br %6 {handshake.bb = 1 : ui32, handshake.name = "br9"} : <i32>
    %35 = br %18 {handshake.bb = 1 : ui32, handshake.name = "br10"} : <i64>
    %36 = br %28 {handshake.bb = 1 : ui32, handshake.name = "br11"} : <i64>
    %37 = br %29 {handshake.bb = 1 : ui32, handshake.name = "br12"} : <i64>
    %38 = br %30 {handshake.bb = 1 : ui32, handshake.name = "br13"} : <i64>
    %39 = br %result {handshake.bb = 1 : ui32, handshake.name = "br14"} : <>
    %40 = mux %index_3 [%31, %trueResult_72] {handshake.bb = 2 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %41 = mux %index_3 [%32, %trueResult_74] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<f32>, <f32>] to <f32>
    %42 = mux %index_3 [%33, %trueResult_76] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<f32>, <f32>] to <f32>
    %43 = mux %index_3 [%34, %trueResult_78] {handshake.bb = 2 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %44 = mux %index_3 [%35, %trueResult_80] {handshake.bb = 2 : ui32, handshake.name = "mux7"} : <i1>, [<i64>, <i64>] to <i64>
    %45 = mux %index_3 [%36, %trueResult_82] {handshake.bb = 2 : ui32, handshake.name = "mux8"} : <i1>, [<i64>, <i64>] to <i64>
    %46 = mux %index_3 [%37, %trueResult_84] {handshake.bb = 2 : ui32, handshake.name = "mux9"} : <i1>, [<i64>, <i64>] to <i64>
    %47 = mux %index_3 [%38, %trueResult_86] {handshake.bb = 2 : ui32, handshake.name = "mux10"} : <i1>, [<i64>, <i64>] to <i64>
    %result_2, %index_3 = control_merge [%39, %trueResult_88]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %48 = constant %result_2 {handshake.bb = 2 : ui32, handshake.name = "constant16", value = 0.000000e+00 : f32} : <>, <f32>
    %49 = source {handshake.bb = 2 : ui32, handshake.name = "source4"} : <>
    %50 = constant %49 {handshake.bb = 2 : ui32, handshake.name = "constant17", value = -1 : i32} : <>, <i32>
    %51 = constant %result_2 {handshake.bb = 2 : ui32, handshake.name = "constant18", value = 0 : i32} : <>, <i32>
    %52 = addi %40, %50 {handshake.bb = 2 : ui32, handshake.name = "addi1"} : <i32>
    %53 = cmpi sgt, %52, %51 {handshake.bb = 2 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %53, %48 {handshake.bb = 2 : ui32, handshake.name = "cond_br4"} : <i1>, <f32>
    %trueResult_4, %falseResult_5 = cond_br %53, %51 {handshake.bb = 2 : ui32, handshake.name = "cond_br5"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %53, %41 {handshake.bb = 2 : ui32, handshake.name = "cond_br6"} : <i1>, <f32>
    %trueResult_8, %falseResult_9 = cond_br %53, %42 {handshake.bb = 2 : ui32, handshake.name = "cond_br7"} : <i1>, <f32>
    %trueResult_10, %falseResult_11 = cond_br %53, %43 {handshake.bb = 2 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %53, %44 {handshake.bb = 2 : ui32, handshake.name = "cond_br9"} : <i1>, <i64>
    %trueResult_14, %falseResult_15 = cond_br %53, %45 {handshake.bb = 2 : ui32, handshake.name = "cond_br10"} : <i1>, <i64>
    %trueResult_16, %falseResult_17 = cond_br %53, %46 {handshake.bb = 2 : ui32, handshake.name = "cond_br11"} : <i1>, <i64>
    %trueResult_18, %falseResult_19 = cond_br %53, %47 {handshake.bb = 2 : ui32, handshake.name = "cond_br12"} : <i1>, <i64>
    %trueResult_20, %falseResult_21 = cond_br %53, %40 {handshake.bb = 2 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_22, %falseResult_23 = cond_br %53, %52 {handshake.bb = 2 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_24, %falseResult_25 = cond_br %53, %result_2 {handshake.bb = 2 : ui32, handshake.name = "cond_br15"} : <i1>, <>
    %54 = mux %index_27 [%trueResult, %trueResult_38] {handshake.bb = 3 : ui32, handshake.name = "mux11"} : <i1>, [<f32>, <f32>] to <f32>
    %55 = mux %index_27 [%trueResult_4, %trueResult_40] {handshake.bb = 3 : ui32, handshake.name = "mux12"} : <i1>, [<i32>, <i32>] to <i32>
    %56 = mux %index_27 [%trueResult_6, %trueResult_42] {handshake.bb = 3 : ui32, handshake.name = "mux13"} : <i1>, [<f32>, <f32>] to <f32>
    %57 = mux %index_27 [%trueResult_8, %trueResult_44] {handshake.bb = 3 : ui32, handshake.name = "mux14"} : <i1>, [<f32>, <f32>] to <f32>
    %58 = mux %index_27 [%trueResult_10, %trueResult_46] {handshake.bb = 3 : ui32, handshake.name = "mux15"} : <i1>, [<i32>, <i32>] to <i32>
    %59 = mux %index_27 [%trueResult_12, %trueResult_48] {handshake.bb = 3 : ui32, handshake.name = "mux16"} : <i1>, [<i64>, <i64>] to <i64>
    %60 = mux %index_27 [%trueResult_14, %trueResult_50] {handshake.bb = 3 : ui32, handshake.name = "mux17"} : <i1>, [<i64>, <i64>] to <i64>
    %61 = mux %index_27 [%trueResult_16, %trueResult_52] {handshake.bb = 3 : ui32, handshake.name = "mux18"} : <i1>, [<i64>, <i64>] to <i64>
    %62 = mux %index_27 [%trueResult_18, %trueResult_54] {handshake.bb = 3 : ui32, handshake.name = "mux19"} : <i1>, [<i64>, <i64>] to <i64>
    %63 = mux %index_27 [%trueResult_20, %trueResult_56] {handshake.bb = 3 : ui32, handshake.name = "mux20"} : <i1>, [<i32>, <i32>] to <i32>
    %64 = mux %index_27 [%trueResult_22, %trueResult_58] {handshake.bb = 3 : ui32, handshake.name = "mux21"} : <i1>, [<i32>, <i32>] to <i32>
    %result_26, %index_27 = control_merge [%trueResult_24, %trueResult_60]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %65 = source {handshake.bb = 3 : ui32, handshake.name = "source5"} : <>
    %66 = constant %65 {handshake.bb = 3 : ui32, handshake.name = "constant19", value = 1 : i32} : <>, <i32>
    %67 = source {handshake.bb = 3 : ui32, handshake.name = "source6"} : <>
    %68 = constant %67 {handshake.bb = 3 : ui32, handshake.name = "constant20", value = 4 : i64} : <>, <i64>
    %69 = source {handshake.bb = 3 : ui32, handshake.name = "source7"} : <>
    %70 = constant %69 {handshake.bb = 3 : ui32, handshake.name = "constant21", value = 3 : i64} : <>, <i64>
    %71 = source {handshake.bb = 3 : ui32, handshake.name = "source8"} : <>
    %72 = constant %71 {handshake.bb = 3 : ui32, handshake.name = "constant22", value = 2 : i64} : <>, <i64>
    %73 = source {handshake.bb = 3 : ui32, handshake.name = "source9"} : <>
    %74 = constant %73 {handshake.bb = 3 : ui32, handshake.name = "constant23", value = 1 : i64} : <>, <i64>
    %75 = extui %55 {handshake.bb = 3 : ui32, handshake.name = "extui5"} : <i32> to <i64>
    %76 = extui %58 {handshake.bb = 3 : ui32, handshake.name = "extui6"} : <i32> to <i64>
    %77 = shli %75, %74 {handshake.bb = 3 : ui32, handshake.name = "shli4"} : <i64>
    %78 = shli %75, %72 {handshake.bb = 3 : ui32, handshake.name = "shli5"} : <i64>
    %79 = addi %77, %78 {handshake.bb = 3 : ui32, handshake.name = "addi16"} : <i64>
    %80 = shli %75, %70 {handshake.bb = 3 : ui32, handshake.name = "shli6"} : <i64>
    %81 = shli %75, %68 {handshake.bb = 3 : ui32, handshake.name = "shli7"} : <i64>
    %82 = addi %80, %81 {handshake.bb = 3 : ui32, handshake.name = "addi17"} : <i64>
    %83 = addi %79, %82 {handshake.bb = 3 : ui32, handshake.name = "addi18"} : <i64>
    %84 = addi %83, %76 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i64>
    %85 = trunci %84 {handshake.bb = 3 : ui32, handshake.name = "index_cast0"} : <i64> to <i32>
    %addressResult, %dataResult = load[%85] %outputs_0#0 {handshake.bb = 3 : ui32, handshake.name = "load0"} : <i32>, <f32>, <i32>, <f32>
    %86 = mulf %dataResult, %56 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "mulf0"} : <f32>
    %87 = extui %58 {handshake.bb = 3 : ui32, handshake.name = "extui7"} : <i32> to <i64>
    %88 = extui %63 {handshake.bb = 3 : ui32, handshake.name = "extui8"} : <i32> to <i64>
    %89 = shli %87, %74 {handshake.bb = 3 : ui32, handshake.name = "shli8"} : <i64>
    %90 = shli %87, %72 {handshake.bb = 3 : ui32, handshake.name = "shli9"} : <i64>
    %91 = addi %89, %90 {handshake.bb = 3 : ui32, handshake.name = "addi19"} : <i64>
    %92 = shli %87, %70 {handshake.bb = 3 : ui32, handshake.name = "shli10"} : <i64>
    %93 = shli %87, %68 {handshake.bb = 3 : ui32, handshake.name = "shli11"} : <i64>
    %94 = addi %92, %93 {handshake.bb = 3 : ui32, handshake.name = "addi20"} : <i64>
    %95 = addi %91, %94 {handshake.bb = 3 : ui32, handshake.name = "addi21"} : <i64>
    %96 = addi %95, %88 {handshake.bb = 3 : ui32, handshake.name = "addi3"} : <i64>
    %97 = trunci %96 {handshake.bb = 3 : ui32, handshake.name = "index_cast1"} : <i64> to <i32>
    %addressResult_28, %dataResult_29 = load[%97] %outputs#0 {handshake.bb = 3 : ui32, handshake.name = "load1"} : <i32>, <f32>, <i32>, <f32>
    %98 = mulf %86, %dataResult_29 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "mulf1"} : <f32>
    %99 = extui %55 {handshake.bb = 3 : ui32, handshake.name = "extui9"} : <i32> to <i64>
    %100 = extui %63 {handshake.bb = 3 : ui32, handshake.name = "extui10"} : <i32> to <i64>
    %101 = shli %99, %74 {handshake.bb = 3 : ui32, handshake.name = "shli12"} : <i64>
    %102 = shli %99, %72 {handshake.bb = 3 : ui32, handshake.name = "shli13"} : <i64>
    %103 = addi %101, %102 {handshake.bb = 3 : ui32, handshake.name = "addi22"} : <i64>
    %104 = shli %99, %70 {handshake.bb = 3 : ui32, handshake.name = "shli14"} : <i64>
    %105 = shli %99, %68 {handshake.bb = 3 : ui32, handshake.name = "shli15"} : <i64>
    %106 = addi %104, %105 {handshake.bb = 3 : ui32, handshake.name = "addi23"} : <i64>
    %107 = addi %103, %106 {handshake.bb = 3 : ui32, handshake.name = "addi24"} : <i64>
    %108 = addi %107, %100 {handshake.bb = 3 : ui32, handshake.name = "addi4"} : <i64>
    %109 = trunci %108 {handshake.bb = 3 : ui32, handshake.name = "index_cast2"} : <i64> to <i32>
    %addressResult_30, %dataResult_31 = load[%109] %0#0 {handshake.bb = 3 : ui32, handshake.name = "load2"} : <i32>, <f32>, <i32>, <f32>
    %110 = addf %dataResult_31, %98 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "addf0"} : <f32>
    %111 = trunci %108 {handshake.bb = 3 : ui32, handshake.name = "index_cast3"} : <i64> to <i32>
    %addressResult_32, %dataResult_33 = store[%111] %110 {handshake.bb = 3 : ui32, handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store9", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store3"} : <i32>, <f32>, <i32>, <f32>
    %112 = extui %55 {handshake.bb = 3 : ui32, handshake.name = "extui11"} : <i32> to <i64>
    %113 = extui %63 {handshake.bb = 3 : ui32, handshake.name = "extui12"} : <i32> to <i64>
    %114 = shli %112, %74 {handshake.bb = 3 : ui32, handshake.name = "shli16"} : <i64>
    %115 = shli %112, %72 {handshake.bb = 3 : ui32, handshake.name = "shli17"} : <i64>
    %116 = addi %114, %115 {handshake.bb = 3 : ui32, handshake.name = "addi25"} : <i64>
    %117 = shli %112, %70 {handshake.bb = 3 : ui32, handshake.name = "shli18"} : <i64>
    %118 = shli %112, %68 {handshake.bb = 3 : ui32, handshake.name = "shli19"} : <i64>
    %119 = addi %117, %118 {handshake.bb = 3 : ui32, handshake.name = "addi26"} : <i64>
    %120 = addi %116, %119 {handshake.bb = 3 : ui32, handshake.name = "addi27"} : <i64>
    %121 = addi %120, %113 {handshake.bb = 3 : ui32, handshake.name = "addi5"} : <i64>
    %122 = trunci %121 {handshake.bb = 3 : ui32, handshake.name = "index_cast4"} : <i64> to <i32>
    %addressResult_34, %dataResult_35 = load[%122] %outputs#1 {handshake.bb = 3 : ui32, handshake.name = "load4"} : <i32>, <f32>, <i32>, <f32>
    %123 = extui %55 {handshake.bb = 3 : ui32, handshake.name = "extui13"} : <i32> to <i64>
    %124 = extui %58 {handshake.bb = 3 : ui32, handshake.name = "extui14"} : <i32> to <i64>
    %125 = shli %123, %74 {handshake.bb = 3 : ui32, handshake.name = "shli20"} : <i64>
    %126 = shli %123, %72 {handshake.bb = 3 : ui32, handshake.name = "shli21"} : <i64>
    %127 = addi %125, %126 {handshake.bb = 3 : ui32, handshake.name = "addi28"} : <i64>
    %128 = shli %123, %70 {handshake.bb = 3 : ui32, handshake.name = "shli22"} : <i64>
    %129 = shli %123, %68 {handshake.bb = 3 : ui32, handshake.name = "shli23"} : <i64>
    %130 = addi %128, %129 {handshake.bb = 3 : ui32, handshake.name = "addi29"} : <i64>
    %131 = addi %127, %130 {handshake.bb = 3 : ui32, handshake.name = "addi30"} : <i64>
    %132 = addi %131, %124 {handshake.bb = 3 : ui32, handshake.name = "addi6"} : <i64>
    %133 = trunci %132 {handshake.bb = 3 : ui32, handshake.name = "index_cast5"} : <i64> to <i32>
    %addressResult_36, %dataResult_37 = load[%133] %outputs_0#1 {handshake.bb = 3 : ui32, handshake.name = "load5"} : <i32>, <f32>, <i32>, <f32>
    %134 = mulf %dataResult_35, %dataResult_37 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "mulf2"} : <f32>
    %135 = addf %54, %134 {fastmath = #arith.fastmath<none>, handshake.bb = 3 : ui32, handshake.name = "addf1"} : <f32>
    %136 = addi %55, %66 {handshake.bb = 3 : ui32, handshake.name = "addi7"} : <i32>
    %137 = cmpi slt, %136, %64 {handshake.bb = 3 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_38, %falseResult_39 = cond_br %137, %135 {handshake.bb = 3 : ui32, handshake.name = "cond_br16"} : <i1>, <f32>
    %trueResult_40, %falseResult_41 = cond_br %137, %136 {handshake.bb = 3 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    %trueResult_42, %falseResult_43 = cond_br %137, %56 {handshake.bb = 3 : ui32, handshake.name = "cond_br18"} : <i1>, <f32>
    %trueResult_44, %falseResult_45 = cond_br %137, %57 {handshake.bb = 3 : ui32, handshake.name = "cond_br19"} : <i1>, <f32>
    %trueResult_46, %falseResult_47 = cond_br %137, %58 {handshake.bb = 3 : ui32, handshake.name = "cond_br20"} : <i1>, <i32>
    %trueResult_48, %falseResult_49 = cond_br %137, %59 {handshake.bb = 3 : ui32, handshake.name = "cond_br21"} : <i1>, <i64>
    %trueResult_50, %falseResult_51 = cond_br %137, %60 {handshake.bb = 3 : ui32, handshake.name = "cond_br22"} : <i1>, <i64>
    %trueResult_52, %falseResult_53 = cond_br %137, %61 {handshake.bb = 3 : ui32, handshake.name = "cond_br23"} : <i1>, <i64>
    %trueResult_54, %falseResult_55 = cond_br %137, %62 {handshake.bb = 3 : ui32, handshake.name = "cond_br24"} : <i1>, <i64>
    %trueResult_56, %falseResult_57 = cond_br %137, %63 {handshake.bb = 3 : ui32, handshake.name = "cond_br25"} : <i1>, <i32>
    %trueResult_58, %falseResult_59 = cond_br %137, %64 {handshake.bb = 3 : ui32, handshake.name = "cond_br26"} : <i1>, <i32>
    %trueResult_60, %falseResult_61 = cond_br %137, %result_26 {handshake.bb = 3 : ui32, handshake.name = "cond_br27"} : <i1>, <>
    %138 = mux %index_63 [%falseResult, %falseResult_39] {handshake.bb = 4 : ui32, handshake.name = "mux22"} : <i1>, [<f32>, <f32>] to <f32>
    %139 = mux %index_63 [%falseResult_7, %falseResult_43] {handshake.bb = 4 : ui32, handshake.name = "mux23"} : <i1>, [<f32>, <f32>] to <f32>
    %140 = mux %index_63 [%falseResult_9, %falseResult_45] {handshake.bb = 4 : ui32, handshake.name = "mux24"} : <i1>, [<f32>, <f32>] to <f32>
    %141 = mux %index_63 [%falseResult_11, %falseResult_47] {handshake.bb = 4 : ui32, handshake.name = "mux25"} : <i1>, [<i32>, <i32>] to <i32>
    %142 = mux %index_63 [%falseResult_13, %falseResult_49] {handshake.bb = 4 : ui32, handshake.name = "mux26"} : <i1>, [<i64>, <i64>] to <i64>
    %143 = mux %index_63 [%falseResult_15, %falseResult_51] {handshake.bb = 4 : ui32, handshake.name = "mux27"} : <i1>, [<i64>, <i64>] to <i64>
    %144 = mux %index_63 [%falseResult_17, %falseResult_53] {handshake.bb = 4 : ui32, handshake.name = "mux28"} : <i1>, [<i64>, <i64>] to <i64>
    %145 = mux %index_63 [%falseResult_19, %falseResult_55] {handshake.bb = 4 : ui32, handshake.name = "mux29"} : <i1>, [<i64>, <i64>] to <i64>
    %146 = mux %index_63 [%falseResult_21, %falseResult_57] {handshake.bb = 4 : ui32, handshake.name = "mux30"} : <i1>, [<i32>, <i32>] to <i32>
    %result_62, %index_63 = control_merge [%falseResult_25, %falseResult_61]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %147 = source {handshake.bb = 4 : ui32, handshake.name = "source10"} : <>
    %148 = constant %147 {handshake.bb = 4 : ui32, handshake.name = "constant24", value = 30 : i32} : <>, <i32>
    %149 = source {handshake.bb = 4 : ui32, handshake.name = "source11"} : <>
    %150 = constant %149 {handshake.bb = 4 : ui32, handshake.name = "constant25", value = 1 : i32} : <>, <i32>
    %151 = source {handshake.bb = 4 : ui32, handshake.name = "source12"} : <>
    %152 = constant %151 {handshake.bb = 4 : ui32, handshake.name = "constant26", value = 4 : i64} : <>, <i64>
    %153 = source {handshake.bb = 4 : ui32, handshake.name = "source13"} : <>
    %154 = constant %153 {handshake.bb = 4 : ui32, handshake.name = "constant27", value = 3 : i64} : <>, <i64>
    %155 = source {handshake.bb = 4 : ui32, handshake.name = "source14"} : <>
    %156 = constant %155 {handshake.bb = 4 : ui32, handshake.name = "constant28", value = 2 : i64} : <>, <i64>
    %157 = source {handshake.bb = 4 : ui32, handshake.name = "source15"} : <>
    %158 = constant %157 {handshake.bb = 4 : ui32, handshake.name = "constant29", value = 1 : i64} : <>, <i64>
    %159 = extui %146 {handshake.bb = 4 : ui32, handshake.name = "extui15"} : <i32> to <i64>
    %160 = shli %142, %158 {handshake.bb = 4 : ui32, handshake.name = "shli24"} : <i64>
    %161 = shli %142, %156 {handshake.bb = 4 : ui32, handshake.name = "shli25"} : <i64>
    %162 = addi %160, %161 {handshake.bb = 4 : ui32, handshake.name = "addi31"} : <i64>
    %163 = shli %142, %154 {handshake.bb = 4 : ui32, handshake.name = "shli26"} : <i64>
    %164 = shli %142, %152 {handshake.bb = 4 : ui32, handshake.name = "shli27"} : <i64>
    %165 = addi %163, %164 {handshake.bb = 4 : ui32, handshake.name = "addi32"} : <i64>
    %166 = addi %162, %165 {handshake.bb = 4 : ui32, handshake.name = "addi33"} : <i64>
    %167 = addi %166, %159 {handshake.bb = 4 : ui32, handshake.name = "addi8"} : <i64>
    %168 = trunci %167 {handshake.bb = 4 : ui32, handshake.name = "index_cast6"} : <i64> to <i32>
    %addressResult_64, %dataResult_65 = load[%168] %0#1 {handshake.bb = 4 : ui32, handshake.name = "load6"} : <i32>, <f32>, <i32>, <f32>
    %169 = mulf %dataResult_65, %140 {fastmath = #arith.fastmath<none>, handshake.bb = 4 : ui32, handshake.name = "mulf3"} : <f32>
    %170 = trunci %143 {handshake.bb = 4 : ui32, handshake.name = "index_cast7"} : <i64> to <i32>
    %addressResult_66, %dataResult_67 = load[%170] %outputs_0#2 {handshake.bb = 4 : ui32, handshake.name = "load7"} : <i32>, <f32>, <i32>, <f32>
    %171 = mulf %dataResult_67, %139 {fastmath = #arith.fastmath<none>, handshake.bb = 4 : ui32, handshake.name = "mulf4"} : <f32>
    %172 = extui %146 {handshake.bb = 4 : ui32, handshake.name = "extui16"} : <i32> to <i64>
    %173 = shli %144, %158 {handshake.bb = 4 : ui32, handshake.name = "shli28"} : <i64>
    %174 = shli %144, %156 {handshake.bb = 4 : ui32, handshake.name = "shli29"} : <i64>
    %175 = addi %173, %174 {handshake.bb = 4 : ui32, handshake.name = "addi34"} : <i64>
    %176 = shli %144, %154 {handshake.bb = 4 : ui32, handshake.name = "shli30"} : <i64>
    %177 = shli %144, %152 {handshake.bb = 4 : ui32, handshake.name = "shli31"} : <i64>
    %178 = addi %176, %177 {handshake.bb = 4 : ui32, handshake.name = "addi35"} : <i64>
    %179 = addi %175, %178 {handshake.bb = 4 : ui32, handshake.name = "addi36"} : <i64>
    %180 = addi %179, %172 {handshake.bb = 4 : ui32, handshake.name = "addi9"} : <i64>
    %181 = trunci %180 {handshake.bb = 4 : ui32, handshake.name = "index_cast8"} : <i64> to <i32>
    %addressResult_68, %dataResult_69 = load[%181] %outputs#2 {handshake.bb = 4 : ui32, handshake.name = "load8"} : <i32>, <f32>, <i32>, <f32>
    %182 = mulf %171, %dataResult_69 {fastmath = #arith.fastmath<none>, handshake.bb = 4 : ui32, handshake.name = "mulf5"} : <f32>
    %183 = addf %169, %182 {fastmath = #arith.fastmath<none>, handshake.bb = 4 : ui32, handshake.name = "addf2"} : <f32>
    %184 = mulf %138, %139 {fastmath = #arith.fastmath<none>, handshake.bb = 4 : ui32, handshake.name = "mulf6"} : <f32>
    %185 = addf %183, %184 {fastmath = #arith.fastmath<none>, handshake.bb = 4 : ui32, handshake.name = "addf3"} : <f32>
    %186 = extui %146 {handshake.bb = 4 : ui32, handshake.name = "extui17"} : <i32> to <i64>
    %187 = shli %145, %158 {handshake.bb = 4 : ui32, handshake.name = "shli32"} : <i64>
    %188 = shli %145, %156 {handshake.bb = 4 : ui32, handshake.name = "shli33"} : <i64>
    %189 = addi %187, %188 {handshake.bb = 4 : ui32, handshake.name = "addi37"} : <i64>
    %190 = shli %145, %154 {handshake.bb = 4 : ui32, handshake.name = "shli34"} : <i64>
    %191 = shli %145, %152 {handshake.bb = 4 : ui32, handshake.name = "shli35"} : <i64>
    %192 = addi %190, %191 {handshake.bb = 4 : ui32, handshake.name = "addi38"} : <i64>
    %193 = addi %189, %192 {handshake.bb = 4 : ui32, handshake.name = "addi39"} : <i64>
    %194 = addi %193, %186 {handshake.bb = 4 : ui32, handshake.name = "addi10"} : <i64>
    %195 = trunci %194 {handshake.bb = 4 : ui32, handshake.name = "index_cast9"} : <i64> to <i32>
    %addressResult_70, %dataResult_71 = store[%195] %185 {handshake.bb = 4 : ui32, handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store9"} : <i32>, <f32>, <i32>, <f32>
    %196 = addi %146, %150 {handshake.bb = 4 : ui32, handshake.name = "addi11"} : <i32>
    %197 = cmpi ult, %196, %148 {handshake.bb = 4 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_72, %falseResult_73 = cond_br %197, %196 {handshake.bb = 4 : ui32, handshake.name = "cond_br28"} : <i1>, <i32>
    %trueResult_74, %falseResult_75 = cond_br %197, %139 {handshake.bb = 4 : ui32, handshake.name = "cond_br29"} : <i1>, <f32>
    %trueResult_76, %falseResult_77 = cond_br %197, %140 {handshake.bb = 4 : ui32, handshake.name = "cond_br30"} : <i1>, <f32>
    %trueResult_78, %falseResult_79 = cond_br %197, %141 {handshake.bb = 4 : ui32, handshake.name = "cond_br31"} : <i1>, <i32>
    %trueResult_80, %falseResult_81 = cond_br %197, %142 {handshake.bb = 4 : ui32, handshake.name = "cond_br32"} : <i1>, <i64>
    %trueResult_82, %falseResult_83 = cond_br %197, %143 {handshake.bb = 4 : ui32, handshake.name = "cond_br33"} : <i1>, <i64>
    %trueResult_84, %falseResult_85 = cond_br %197, %144 {handshake.bb = 4 : ui32, handshake.name = "cond_br34"} : <i1>, <i64>
    %trueResult_86, %falseResult_87 = cond_br %197, %145 {handshake.bb = 4 : ui32, handshake.name = "cond_br35"} : <i1>, <i64>
    %trueResult_88, %falseResult_89 = cond_br %197, %result_62 {handshake.bb = 4 : ui32, handshake.name = "cond_br36"} : <i1>, <>
    %198 = merge %falseResult_75 {handshake.bb = 5 : ui32, handshake.name = "merge0"} : <f32>
    %199 = merge %falseResult_77 {handshake.bb = 5 : ui32, handshake.name = "merge1"} : <f32>
    %200 = merge %falseResult_79 {handshake.bb = 5 : ui32, handshake.name = "merge2"} : <i32>
    %result_90, %index_91 = control_merge [%falseResult_89]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>] to <>, <i1>
    %201 = source {handshake.bb = 5 : ui32, handshake.name = "source16"} : <>
    %202 = constant %201 {handshake.bb = 5 : ui32, handshake.name = "constant30", value = 10 : i32} : <>, <i32>
    %203 = source {handshake.bb = 5 : ui32, handshake.name = "source17"} : <>
    %204 = constant %203 {handshake.bb = 5 : ui32, handshake.name = "constant31", value = 1 : i32} : <>, <i32>
    %205 = addi %200, %204 {handshake.bb = 5 : ui32, handshake.name = "addi12"} : <i32>
    %206 = cmpi ult, %205, %202 {handshake.bb = 5 : ui32, handshake.name = "cmpi3"} : <i32>
    %trueResult_92, %falseResult_93 = cond_br %206, %205 {handshake.bb = 5 : ui32, handshake.name = "cond_br37"} : <i1>, <i32>
    %trueResult_94, %falseResult_95 = cond_br %206, %198 {handshake.bb = 5 : ui32, handshake.name = "cond_br38"} : <i1>, <f32>
    %trueResult_96, %falseResult_97 = cond_br %206, %199 {handshake.bb = 5 : ui32, handshake.name = "cond_br39"} : <i1>, <f32>
    %trueResult_98, %falseResult_99 = cond_br %206, %result_90 {handshake.bb = 5 : ui32, handshake.name = "cond_br40"} : <i1>, <>
    %result_100, %index_101 = control_merge [%falseResult_99]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>] to <>, <i1>
    end {handshake.bb = 6 : ui32, handshake.name = "end0"} %memEnd_1, %memEnd, %0#2, %arg8 : <>, <>, <>, <>
  }
}

