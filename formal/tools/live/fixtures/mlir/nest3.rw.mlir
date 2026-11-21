module {
  handshake.func @nest3(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["a", "b", "start"], resNames = ["out0", "end"]} {
    %0:5 = fork [5] %arg2 {handshake.bb = 0 : ui32, handshake.name = "fork0"} : <>
    %1:2 = fork [2] %arg0 {handshake.bb = 0 : ui32, handshake.name = "fork1"} : <i32>
    %2 = constant %0#4 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %3 = cmpi sgt, %1#1, %2 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %4:5 = fork [5] %3 {handshake.bb = 0 : ui32, handshake.name = "fork2"} : <i1>
    %5 = constant %0#0 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = -56507 : i17} : <>, <i17>
    %trueResult, %falseResult = cond_br %4#0, %5 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <i17>
    %6 = extui %falseResult {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i17> to <i32>
    %7 = extui %trueResult {handshake.bb = 0 : ui32, handshake.name = "extui1"} : <i17> to <i32>
    %8 = constant %0#1 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = false} : <>, <i1>
    %trueResult_0, %falseResult_1 = cond_br %4#1, %8 {handshake.bb = 0 : ui32, handshake.name = "cond_br7"} : <i1>, <i1>
    sink %falseResult_1 {handshake.name = "sink0"} : <i1>
    %9 = extui %trueResult_0 {handshake.bb = 0 : ui32, handshake.name = "extui2"} : <i1> to <i32>
    %trueResult_2, %falseResult_3 = cond_br %4#4, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    sink %falseResult_3 {handshake.name = "sink1"} : <i32>
    %trueResult_4, %falseResult_5 = cond_br %4#3, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    sink %falseResult_5 {handshake.name = "sink2"} : <i32>
    %trueResult_6, %falseResult_7 = cond_br %4#2, %0#3 {handshake.bb = 0 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %10 = mux %15#0 [%7, %trueResult_72] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %11 = mux %15#1 [%9, %trueResult_74] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %12 = mux %15#2 [%trueResult_2, %trueResult_76] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %13 = mux %15#3 [%trueResult_4, %trueResult_78] {handshake.bb = 1 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %14:2 = fork [2] %13 {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <i32>
    %result, %index = control_merge [%trueResult_6, %trueResult_80]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %15:4 = fork [4] %index {handshake.bb = 1 : ui32, handshake.name = "fork4"} : <i1>
    %16:3 = fork [3] %result {handshake.bb = 1 : ui32, handshake.name = "fork5"} : <>
    %17 = constant %16#2 {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 0 : i32} : <>, <i32>
    %18 = cmpi sgt, %14#1, %17 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %19:6 = fork [6] %18 {handshake.bb = 1 : ui32, handshake.name = "fork6"} : <i1>
    %20 = constant %16#0 {handshake.bb = 1 : ui32, handshake.name = "constant4", value = false} : <>, <i1>
    %trueResult_8, %falseResult_9 = cond_br %19#0, %20 {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <i1>
    sink %falseResult_9 {handshake.name = "sink3"} : <i1>
    %21 = extui %trueResult_8 {handshake.bb = 1 : ui32, handshake.name = "extui3"} : <i1> to <i32>
    %trueResult_10, %falseResult_11 = cond_br %19#5, %10 {handshake.bb = 1 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %19#4, %12 {handshake.bb = 1 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %19#3, %14#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %19#2, %11 {handshake.bb = 1 : ui32, handshake.name = "cond_br15"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %19#1, %16#1 {handshake.bb = 1 : ui32, handshake.name = "cond_br16"} : <i1>, <>
    %22 = mux %29#0 [%21, %trueResult_58] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %23:2 = fork [2] %22 {handshake.bb = 2 : ui32, handshake.name = "fork7"} : <i32>
    %24 = mux %29#1 [%trueResult_10, %trueResult_60] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %25 = mux %29#2 [%trueResult_12, %trueResult_62] {handshake.bb = 2 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %26 = mux %29#3 [%trueResult_14, %trueResult_64] {handshake.bb = 2 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %27 = mux %29#4 [%trueResult_16, %trueResult_66] {handshake.bb = 2 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %28:2 = fork [2] %27 {handshake.bb = 2 : ui32, handshake.name = "fork8"} : <i32>
    %result_20, %index_21 = control_merge [%trueResult_18, %trueResult_68]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %29:5 = fork [5] %index_21 {handshake.bb = 2 : ui32, handshake.name = "fork9"} : <i1>
    %30:3 = fork [3] %result_20 {handshake.bb = 2 : ui32, handshake.name = "fork10"} : <>
    %31 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %32 = xori %28#1, %23#1 {handshake.bb = 2 : ui32, handshake.name = "xori0"} : <i32>
    %33 = trunci %32 {handshake.bb = 2 : ui32, handshake.name = "trunci0"} : <i32> to <i2>
    %34 = constant %31 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = -1 : i2} : <>, <i2>
    %35 = andi %33, %34 {handshake.bb = 2 : ui32, handshake.name = "andi0"} : <i2>
    %36:2 = fork [2] %35 {handshake.bb = 2 : ui32, handshake.name = "fork11"} : <i2>
    %37 = constant %30#0 {handshake.bb = 2 : ui32, handshake.name = "constant6", value = 0 : i2} : <>, <i2>
    %38 = cmpi ugt, %36#1, %37 {handshake.bb = 2 : ui32, handshake.name = "cmpi2"} : <i2>
    %39:8 = fork [8] %38 {handshake.bb = 2 : ui32, handshake.name = "fork12"} : <i1>
    %40 = constant %30#1 {handshake.bb = 2 : ui32, handshake.name = "constant16", value = false} : <>, <i1>
    %trueResult_22, %falseResult_23 = cond_br %39#7, %40 {handshake.bb = 2 : ui32, handshake.name = "cond_br17"} : <i1>, <i1>
    sink %falseResult_23 {handshake.name = "sink4"} : <i1>
    %41 = extui %trueResult_22 {handshake.bb = 2 : ui32, handshake.name = "extui4"} : <i1> to <i2>
    %trueResult_24, %falseResult_25 = cond_br %39#1, %24 {handshake.bb = 2 : ui32, handshake.name = "cond_br18"} : <i1>, <i32>
    %trueResult_26, %falseResult_27 = cond_br %39#2, %25 {handshake.bb = 2 : ui32, handshake.name = "cond_br19"} : <i1>, <i32>
    %trueResult_28, %falseResult_29 = cond_br %39#3, %26 {handshake.bb = 2 : ui32, handshake.name = "cond_br20"} : <i1>, <i32>
    %trueResult_30, %falseResult_31 = cond_br %39#4, %28#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br21"} : <i1>, <i32>
    %trueResult_32, %falseResult_33 = cond_br %39#5, %23#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br22"} : <i1>, <i32>
    %trueResult_34, %falseResult_35 = cond_br %39#0, %36#0 {handshake.bb = 2 : ui32, handshake.name = "cond_br23"} : <i1>, <i2>
    sink %falseResult_35 {handshake.name = "sink5"} : <i2>
    %trueResult_36, %falseResult_37 = cond_br %39#6, %30#2 {handshake.bb = 2 : ui32, handshake.name = "cond_br24"} : <i1>, <>
    %42 = mux %58#0 [%41, %trueResult_40] {handshake.bb = 3 : ui32, handshake.name = "mux9"} : <i1>, [<i2>, <i2>] to <i2>
    %43:2 = fork [2] %42 {handshake.bb = 3 : ui32, handshake.name = "fork13"} : <i2>
    %44 = extui %43#0 {handshake.bb = 3 : ui32, handshake.name = "extui5"} : <i2> to <i3>
    %45 = constant %60#0 {handshake.bb = 3 : ui32, handshake.name = "constant17", value = 1 : i3} : <>, <i3>
    %46 = extui %43#1 {handshake.bb = 3 : ui32, handshake.name = "extui6"} : <i2> to <i32>
    %47 = mux %58#2 [%trueResult_24, %trueResult_42] {handshake.bb = 3 : ui32, handshake.name = "mux10"} : <i1>, [<i32>, <i32>] to <i32>
    %48:2 = fork [2] %47 {handshake.bb = 3 : ui32, handshake.name = "fork14"} : <i32>
    %49 = mux %58#3 [%trueResult_26, %trueResult_44] {handshake.bb = 3 : ui32, handshake.name = "mux11"} : <i1>, [<i32>, <i32>] to <i32>
    %50 = mux %58#4 [%trueResult_28, %trueResult_46] {handshake.bb = 3 : ui32, handshake.name = "mux12"} : <i1>, [<i32>, <i32>] to <i32>
    %51 = mux %58#5 [%trueResult_30, %trueResult_48] {handshake.bb = 3 : ui32, handshake.name = "mux13"} : <i1>, [<i32>, <i32>] to <i32>
    %52:2 = fork [2] %51 {handshake.bb = 3 : ui32, handshake.name = "fork15"} : <i32>
    %53 = mux %58#6 [%trueResult_32, %trueResult_50] {handshake.bb = 3 : ui32, handshake.name = "mux14"} : <i1>, [<i32>, <i32>] to <i32>
    %54:2 = fork [2] %53 {handshake.bb = 3 : ui32, handshake.name = "fork16"} : <i32>
    %55 = mux %58#1 [%trueResult_34, %trueResult_52] {handshake.bb = 3 : ui32, handshake.name = "mux15"} : <i1>, [<i2>, <i2>] to <i2>
    %56:2 = fork [2] %55 {handshake.bb = 3 : ui32, handshake.name = "fork17"} : <i2>
    %57 = extui %56#0 {handshake.bb = 3 : ui32, handshake.name = "extui7"} : <i2> to <i3>
    %result_38, %index_39 = control_merge [%trueResult_36, %trueResult_54]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %58:7 = fork [7] %index_39 {handshake.bb = 3 : ui32, handshake.name = "fork18"} : <i1>
    %59 = source {handshake.bb = 3 : ui32, handshake.name = "source1"} : <>
    %60:2 = fork [2] %59 {handshake.bb = 3 : ui32, handshake.name = "fork19"} : <>
    %61 = constant %60#1 {handshake.bb = 3 : ui32, handshake.name = "constant10", value = 1 : i32} : <>, <i32>
    %62 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %63 = constant %62 {handshake.bb = 3 : ui32, handshake.name = "constant11", value = 2 : i32} : <>, <i32>
    %64 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %65 = constant %64 {handshake.bb = 3 : ui32, handshake.name = "constant12", value = 4 : i32} : <>, <i32>
    %66 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %67 = constant %66 {handshake.bb = 3 : ui32, handshake.name = "constant13", value = 5 : i32} : <>, <i32>
    %68 = shrui %48#1, %67 {handshake.bb = 3 : ui32, handshake.name = "shrui0"} : <i32>
    %69 = xori %48#0, %68 {handshake.bb = 3 : ui32, handshake.name = "xori1"} : <i32>
    %70 = shli %52#1, %65 {handshake.bb = 3 : ui32, handshake.name = "shli0"} : <i32>
    %71 = shli %54#1, %63 {handshake.bb = 3 : ui32, handshake.name = "shli1"} : <i32>
    %72 = xori %70, %71 {handshake.bb = 3 : ui32, handshake.name = "xori2"} : <i32>
    %73 = xori %72, %46 {handshake.bb = 3 : ui32, handshake.name = "xori3"} : <i32>
    %74 = addi %69, %73 {handshake.bb = 3 : ui32, handshake.name = "addi0"} : <i32>
    %75 = addi %74, %61 {handshake.bb = 3 : ui32, handshake.name = "addi1"} : <i32>
    %76 = addi %44, %45 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i3>
    %77:2 = fork [2] %76 {handshake.bb = 3 : ui32, handshake.name = "fork20"} : <i3>
    %78 = trunci %77#0 {handshake.bb = 3 : ui32, handshake.name = "trunci1"} : <i3> to <i2>
    %79 = cmpi ult, %77#1, %57 {handshake.bb = 3 : ui32, handshake.name = "cmpi3"} : <i3>
    %80:8 = fork [8] %79 {handshake.bb = 3 : ui32, handshake.name = "fork21"} : <i1>
    %trueResult_40, %falseResult_41 = cond_br %80#0, %78 {handshake.bb = 3 : ui32, handshake.name = "cond_br25"} : <i1>, <i2>
    sink %falseResult_41 {handshake.name = "sink6"} : <i2>
    %trueResult_42, %falseResult_43 = cond_br %80#1, %75 {handshake.bb = 3 : ui32, handshake.name = "cond_br26"} : <i1>, <i32>
    %trueResult_44, %falseResult_45 = cond_br %80#2, %49 {handshake.bb = 3 : ui32, handshake.name = "cond_br27"} : <i1>, <i32>
    %trueResult_46, %falseResult_47 = cond_br %80#3, %50 {handshake.bb = 3 : ui32, handshake.name = "cond_br28"} : <i1>, <i32>
    %trueResult_48, %falseResult_49 = cond_br %80#4, %52#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br29"} : <i1>, <i32>
    %trueResult_50, %falseResult_51 = cond_br %80#5, %54#0 {handshake.bb = 3 : ui32, handshake.name = "cond_br30"} : <i1>, <i32>
    %trueResult_52, %falseResult_53 = cond_br %80#7, %56#1 {handshake.bb = 3 : ui32, handshake.name = "cond_br31"} : <i1>, <i2>
    sink %falseResult_53 {handshake.name = "sink7"} : <i2>
    %trueResult_54, %falseResult_55 = cond_br %80#6, %result_38 {handshake.bb = 3 : ui32, handshake.name = "cond_br32"} : <i1>, <>
    %81 = mux %87#0 [%falseResult_25, %falseResult_43] {handshake.bb = 4 : ui32, handshake.name = "mux16"} : <i1>, [<i32>, <i32>] to <i32>
    %82 = mux %87#1 [%falseResult_27, %falseResult_45] {handshake.bb = 4 : ui32, handshake.name = "mux17"} : <i1>, [<i32>, <i32>] to <i32>
    %83 = mux %87#2 [%falseResult_29, %falseResult_47] {handshake.bb = 4 : ui32, handshake.name = "mux18"} : <i1>, [<i32>, <i32>] to <i32>
    %84:2 = fork [2] %83 {handshake.bb = 4 : ui32, handshake.name = "fork22"} : <i32>
    %85 = mux %87#3 [%falseResult_31, %falseResult_49] {handshake.bb = 4 : ui32, handshake.name = "mux19"} : <i1>, [<i32>, <i32>] to <i32>
    %86 = mux %87#4 [%falseResult_33, %falseResult_51] {handshake.bb = 4 : ui32, handshake.name = "mux20"} : <i1>, [<i32>, <i32>] to <i32>
    %result_56, %index_57 = control_merge [%falseResult_37, %falseResult_55]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %87:5 = fork [5] %index_57 {handshake.bb = 4 : ui32, handshake.name = "fork23"} : <i1>
    %88 = source {handshake.bb = 4 : ui32, handshake.name = "source5"} : <>
    %89 = constant %88 {handshake.bb = 4 : ui32, handshake.name = "constant14", value = 1 : i32} : <>, <i32>
    %90 = addi %86, %89 {handshake.bb = 4 : ui32, handshake.name = "addi3"} : <i32>
    %91:2 = fork [2] %90 {handshake.bb = 4 : ui32, handshake.name = "fork24"} : <i32>
    %92 = cmpi slt, %91#1, %84#1 {handshake.bb = 4 : ui32, handshake.name = "cmpi4"} : <i32>
    %93:6 = fork [6] %92 {handshake.bb = 4 : ui32, handshake.name = "fork25"} : <i1>
    %trueResult_58, %falseResult_59 = cond_br %93#5, %91#0 {handshake.bb = 4 : ui32, handshake.name = "cond_br33"} : <i1>, <i32>
    sink %falseResult_59 {handshake.name = "sink8"} : <i32>
    %trueResult_60, %falseResult_61 = cond_br %93#4, %81 {handshake.bb = 4 : ui32, handshake.name = "cond_br34"} : <i1>, <i32>
    %trueResult_62, %falseResult_63 = cond_br %93#3, %82 {handshake.bb = 4 : ui32, handshake.name = "cond_br35"} : <i1>, <i32>
    %trueResult_64, %falseResult_65 = cond_br %93#2, %84#0 {handshake.bb = 4 : ui32, handshake.name = "cond_br36"} : <i1>, <i32>
    %trueResult_66, %falseResult_67 = cond_br %93#1, %85 {handshake.bb = 4 : ui32, handshake.name = "cond_br37"} : <i1>, <i32>
    %trueResult_68, %falseResult_69 = cond_br %93#0, %result_56 {handshake.bb = 4 : ui32, handshake.name = "cond_br38"} : <i1>, <>
    %94 = mux %99#0 [%falseResult_11, %falseResult_61] {handshake.bb = 5 : ui32, handshake.name = "mux21"} : <i1>, [<i32>, <i32>] to <i32>
    %95 = mux %99#1 [%falseResult_13, %falseResult_63] {handshake.bb = 5 : ui32, handshake.name = "mux22"} : <i1>, [<i32>, <i32>] to <i32>
    %96:2 = fork [2] %95 {handshake.bb = 5 : ui32, handshake.name = "fork26"} : <i32>
    %97 = mux %99#2 [%falseResult_15, %falseResult_65] {handshake.bb = 5 : ui32, handshake.name = "mux23"} : <i1>, [<i32>, <i32>] to <i32>
    %98 = mux %99#3 [%falseResult_17, %falseResult_67] {handshake.bb = 5 : ui32, handshake.name = "mux24"} : <i1>, [<i32>, <i32>] to <i32>
    %result_70, %index_71 = control_merge [%falseResult_19, %falseResult_69]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    %99:4 = fork [4] %index_71 {handshake.bb = 5 : ui32, handshake.name = "fork27"} : <i1>
    %100 = source {handshake.bb = 5 : ui32, handshake.name = "source6"} : <>
    %101 = constant %100 {handshake.bb = 5 : ui32, handshake.name = "constant15", value = 1 : i32} : <>, <i32>
    %102 = addi %98, %101 {handshake.bb = 5 : ui32, handshake.name = "addi4"} : <i32>
    %103:2 = fork [2] %102 {handshake.bb = 5 : ui32, handshake.name = "fork28"} : <i32>
    %104 = cmpi slt, %103#1, %96#1 {handshake.bb = 5 : ui32, handshake.name = "cmpi5"} : <i32>
    %105:5 = fork [5] %104 {handshake.bb = 5 : ui32, handshake.name = "fork29"} : <i1>
    %trueResult_72, %falseResult_73 = cond_br %105#4, %94 {handshake.bb = 5 : ui32, handshake.name = "cond_br39"} : <i1>, <i32>
    %trueResult_74, %falseResult_75 = cond_br %105#3, %103#0 {handshake.bb = 5 : ui32, handshake.name = "cond_br40"} : <i1>, <i32>
    sink %falseResult_75 {handshake.name = "sink9"} : <i32>
    %trueResult_76, %falseResult_77 = cond_br %105#2, %96#0 {handshake.bb = 5 : ui32, handshake.name = "cond_br41"} : <i1>, <i32>
    sink %falseResult_77 {handshake.name = "sink10"} : <i32>
    %trueResult_78, %falseResult_79 = cond_br %105#1, %97 {handshake.bb = 5 : ui32, handshake.name = "cond_br42"} : <i1>, <i32>
    sink %falseResult_79 {handshake.name = "sink11"} : <i32>
    %trueResult_80, %falseResult_81 = cond_br %105#0, %result_70 {handshake.bb = 5 : ui32, handshake.name = "cond_br43"} : <i1>, <>
    %106 = mux %index_83 [%6, %falseResult_73] {handshake.bb = 6 : ui32, handshake.name = "mux25"} : <i1>, [<i32>, <i32>] to <i32>
    %result_82, %index_83 = control_merge [%falseResult_7, %falseResult_81]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>, <>] to <>, <i1>
    sink %result_82 {handshake.name = "sink12"} : <>
    end {handshake.bb = 6 : ui32, handshake.name = "end0"} %106, %0#2 : <i32>, <>
  }
}

