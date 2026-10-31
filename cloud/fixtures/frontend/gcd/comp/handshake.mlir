module {
  handshake.func @gcd(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["a", "b", "start"], resNames = ["out0", "end"]} {
    %0 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %1 = constant %0 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %2 = cmpi eq, %arg0, %1 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %2, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %2, %arg2 {handshake.bb = 0 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %trueResult_2, %falseResult_3 = cond_br %2, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %3 = merge %falseResult_3 {handshake.bb = 1 : ui32, handshake.name = "merge0"} : <i32>
    %4 = merge %falseResult {handshake.bb = 1 : ui32, handshake.name = "merge1"} : <i32>
    %result, %index = control_merge [%falseResult_1]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>] to <>, <i1>
    %5 = source {handshake.bb = 1 : ui32, handshake.name = "source1"} : <>
    %6 = constant %5 {handshake.bb = 1 : ui32, handshake.name = "constant3", value = 0 : i32} : <>, <i32>
    %7 = cmpi eq, %4, %6 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_4, %falseResult_5 = cond_br %7, %3 {handshake.bb = 1 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %7, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br13"} : <i1>, <>
    %trueResult_8, %falseResult_9 = cond_br %7, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %8 = merge %falseResult_5 {handshake.bb = 2 : ui32, handshake.name = "merge2"} : <i32>
    %9 = merge %falseResult_9 {handshake.bb = 2 : ui32, handshake.name = "merge3"} : <i32>
    %result_10, %index_11 = control_merge [%falseResult_7]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>] to <>, <i1>
    %10 = source {handshake.bb = 2 : ui32, handshake.name = "source2"} : <>
    %11 = constant %10 {handshake.bb = 2 : ui32, handshake.name = "constant4", value = 1 : i32} : <>, <i32>
    %12 = constant %result_10 {handshake.bb = 2 : ui32, handshake.name = "constant5", value = 0 : i32} : <>, <i32>
    %13 = ori %8, %9 {handshake.bb = 2 : ui32, handshake.name = "ori0"} : <i32>
    %14 = andi %13, %11 {handshake.bb = 2 : ui32, handshake.name = "andi0"} : <i32>
    %15 = cmpi eq, %14, %12 {handshake.bb = 2 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_12, %falseResult_13 = cond_br %15, %8 {handshake.bb = 2 : ui32, handshake.name = "cond_br15"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %15, %9 {handshake.bb = 2 : ui32, handshake.name = "cond_br16"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %15, %12 {handshake.bb = 2 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %15, %result_10 {handshake.bb = 2 : ui32, handshake.name = "cond_br18"} : <i1>, <>
    %16 = mux %index_21 [%trueResult_12, %trueResult_22] {handshake.bb = 3 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %17 = mux %index_21 [%trueResult_14, %trueResult_24] {handshake.bb = 3 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %18 = mux %index_21 [%trueResult_16, %trueResult_26] {handshake.bb = 3 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %result_20, %index_21 = control_merge [%trueResult_18, %trueResult_28]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %19 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %20 = constant %19 {handshake.bb = 3 : ui32, handshake.name = "constant6", value = 1 : i32} : <>, <i32>
    %21 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %22 = constant %21 {handshake.bb = 3 : ui32, handshake.name = "constant7", value = 0 : i32} : <>, <i32>
    %23 = shrsi %16, %20 {handshake.bb = 3 : ui32, handshake.name = "shrsi0"} : <i32>
    %24 = shrsi %17, %20 {handshake.bb = 3 : ui32, handshake.name = "shrsi1"} : <i32>
    %25 = addi %18, %20 {handshake.bb = 3 : ui32, handshake.name = "addi0"} : <i32>
    %26 = ori %23, %24 {handshake.bb = 3 : ui32, handshake.name = "ori1"} : <i32>
    %27 = andi %26, %20 {handshake.bb = 3 : ui32, handshake.name = "andi1"} : <i32>
    %28 = cmpi eq, %27, %22 {handshake.bb = 3 : ui32, handshake.name = "cmpi3"} : <i32>
    %trueResult_22, %falseResult_23 = cond_br %28, %23 {handshake.bb = 3 : ui32, handshake.name = "cond_br19"} : <i1>, <i32>
    %trueResult_24, %falseResult_25 = cond_br %28, %24 {handshake.bb = 3 : ui32, handshake.name = "cond_br20"} : <i1>, <i32>
    %trueResult_26, %falseResult_27 = cond_br %28, %25 {handshake.bb = 3 : ui32, handshake.name = "cond_br21"} : <i1>, <i32>
    %trueResult_28, %falseResult_29 = cond_br %28, %result_20 {handshake.bb = 3 : ui32, handshake.name = "cond_br22"} : <i1>, <>
    %29 = mux %index_31 [%falseResult_17, %falseResult_27] {handshake.bb = 4 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %30 = mux %index_31 [%falseResult_15, %falseResult_25] {handshake.bb = 4 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %31 = mux %index_31 [%falseResult_13, %falseResult_23] {handshake.bb = 4 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %result_30, %index_31 = control_merge [%falseResult_19, %falseResult_29]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %32 = br %31 {handshake.bb = 4 : ui32, handshake.name = "br4"} : <i32>
    %33 = br %29 {handshake.bb = 4 : ui32, handshake.name = "br5"} : <i32>
    %34 = br %30 {handshake.bb = 4 : ui32, handshake.name = "br6"} : <i32>
    %35 = br %result_30 {handshake.bb = 4 : ui32, handshake.name = "br7"} : <>
    %36 = mux %index_33 [%32, %falseResult_43] {handshake.bb = 5 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %37 = mux %index_33 [%33, %falseResult_37] {handshake.bb = 5 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %38 = mux %index_33 [%34, %falseResult_39] {handshake.bb = 5 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %result_32, %index_33 = control_merge [%35, %falseResult_41]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    %39 = source {handshake.bb = 5 : ui32, handshake.name = "source5"} : <>
    %40 = constant %39 {handshake.bb = 5 : ui32, handshake.name = "constant8", value = 1 : i32} : <>, <i32>
    %41 = source {handshake.bb = 5 : ui32, handshake.name = "source6"} : <>
    %42 = constant %41 {handshake.bb = 5 : ui32, handshake.name = "constant9", value = 0 : i32} : <>, <i32>
    %43 = cmpi slt, %36, %40 {handshake.bb = 5 : ui32, handshake.name = "cmpi4"} : <i32>
    %44 = andi %36, %40 {handshake.bb = 5 : ui32, handshake.name = "andi2"} : <i32>
    %45 = cmpi ne, %44, %42 {handshake.bb = 5 : ui32, handshake.name = "cmpi5"} : <i32>
    %46 = ori %45, %43 {handshake.bb = 5 : ui32, handshake.name = "ori2"} : <i1>
    %47 = shrsi %36, %40 {handshake.bb = 5 : ui32, handshake.name = "shrsi2"} : <i32>
    %trueResult_34, %falseResult_35 = cond_br %46, %36 {handshake.bb = 5 : ui32, handshake.name = "cond_br23"} : <i1>, <i32>
    %trueResult_36, %falseResult_37 = cond_br %46, %37 {handshake.bb = 5 : ui32, handshake.name = "cond_br24"} : <i1>, <i32>
    %trueResult_38, %falseResult_39 = cond_br %46, %38 {handshake.bb = 5 : ui32, handshake.name = "cond_br25"} : <i1>, <i32>
    %trueResult_40, %falseResult_41 = cond_br %46, %result_32 {handshake.bb = 5 : ui32, handshake.name = "cond_br26"} : <i1>, <>
    %trueResult_42, %falseResult_43 = cond_br %46, %47 {handshake.bb = 5 : ui32, handshake.name = "cond_br27"} : <i1>, <i32>
    %48 = merge %trueResult_34 {handshake.bb = 6 : ui32, handshake.name = "merge4"} : <i32>
    %49 = merge %trueResult_36 {handshake.bb = 6 : ui32, handshake.name = "merge5"} : <i32>
    %50 = merge %trueResult_38 {handshake.bb = 6 : ui32, handshake.name = "merge6"} : <i32>
    %result_44, %index_45 = control_merge [%trueResult_40]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>] to <>, <i1>
    %51 = br %50 {handshake.bb = 6 : ui32, handshake.name = "br8"} : <i32>
    %52 = br %49 {handshake.bb = 6 : ui32, handshake.name = "br9"} : <i32>
    %53 = br %48 {handshake.bb = 6 : ui32, handshake.name = "br10"} : <i32>
    %54 = br %result_44 {handshake.bb = 6 : ui32, handshake.name = "br11"} : <>
    %55 = mux %index_47 [%51, %falseResult_57] {handshake.bb = 7 : ui32, handshake.name = "mux9"} : <i1>, [<i32>, <i32>] to <i32>
    %56 = mux %index_47 [%52, %falseResult_51] {handshake.bb = 7 : ui32, handshake.name = "mux10"} : <i1>, [<i32>, <i32>] to <i32>
    %57 = mux %index_47 [%53, %falseResult_53] {handshake.bb = 7 : ui32, handshake.name = "mux11"} : <i1>, [<i32>, <i32>] to <i32>
    %result_46, %index_47 = control_merge [%54, %falseResult_55]  {handshake.bb = 7 : ui32, handshake.name = "control_merge6"} : [<>, <>] to <>, <i1>
    %58 = source {handshake.bb = 7 : ui32, handshake.name = "source7"} : <>
    %59 = constant %58 {handshake.bb = 7 : ui32, handshake.name = "constant10", value = 1 : i32} : <>, <i32>
    %60 = source {handshake.bb = 7 : ui32, handshake.name = "source8"} : <>
    %61 = constant %60 {handshake.bb = 7 : ui32, handshake.name = "constant11", value = 0 : i32} : <>, <i32>
    %62 = cmpi slt, %55, %59 {handshake.bb = 7 : ui32, handshake.name = "cmpi6"} : <i32>
    %63 = andi %55, %59 {handshake.bb = 7 : ui32, handshake.name = "andi3"} : <i32>
    %64 = cmpi ne, %63, %61 {handshake.bb = 7 : ui32, handshake.name = "cmpi7"} : <i32>
    %65 = ori %64, %62 {handshake.bb = 7 : ui32, handshake.name = "ori3"} : <i1>
    %66 = shrsi %55, %59 {handshake.bb = 7 : ui32, handshake.name = "shrsi3"} : <i32>
    %trueResult_48, %falseResult_49 = cond_br %65, %55 {handshake.bb = 7 : ui32, handshake.name = "cond_br28"} : <i1>, <i32>
    %trueResult_50, %falseResult_51 = cond_br %65, %56 {handshake.bb = 7 : ui32, handshake.name = "cond_br29"} : <i1>, <i32>
    %trueResult_52, %falseResult_53 = cond_br %65, %57 {handshake.bb = 7 : ui32, handshake.name = "cond_br30"} : <i1>, <i32>
    %trueResult_54, %falseResult_55 = cond_br %65, %result_46 {handshake.bb = 7 : ui32, handshake.name = "cond_br31"} : <i1>, <>
    %trueResult_56, %falseResult_57 = cond_br %65, %66 {handshake.bb = 7 : ui32, handshake.name = "cond_br32"} : <i1>, <i32>
    %67 = merge %trueResult_48 {handshake.bb = 8 : ui32, handshake.name = "merge7"} : <i32>
    %68 = merge %trueResult_50 {handshake.bb = 8 : ui32, handshake.name = "merge8"} : <i32>
    %69 = merge %trueResult_52 {handshake.bb = 8 : ui32, handshake.name = "merge9"} : <i32>
    %result_58, %index_59 = control_merge [%trueResult_54]  {handshake.bb = 8 : ui32, handshake.name = "control_merge7"} : [<>] to <>, <i1>
    %70 = source {handshake.bb = 8 : ui32, handshake.name = "source9"} : <>
    %71 = constant %70 {handshake.bb = 8 : ui32, handshake.name = "constant12", value = 0 : i32} : <>, <i32>
    %72 = cmpi eq, %69, %71 {handshake.bb = 8 : ui32, handshake.name = "cmpi8"} : <i32>
    %trueResult_60, %falseResult_61 = cond_br %72, %67 {handshake.bb = 8 : ui32, handshake.name = "cond_br33"} : <i1>, <i32>
    %trueResult_62, %falseResult_63 = cond_br %72, %68 {handshake.bb = 8 : ui32, handshake.name = "cond_br34"} : <i1>, <i32>
    %trueResult_64, %falseResult_65 = cond_br %72, %result_58 {handshake.bb = 8 : ui32, handshake.name = "cond_br35"} : <i1>, <>
    %trueResult_66, %falseResult_67 = cond_br %72, %69 {handshake.bb = 8 : ui32, handshake.name = "cond_br36"} : <i1>, <i32>
    %73 = merge %trueResult_82 {handshake.bb = 9 : ui32, handshake.name = "merge10"} : <i32>
    %74 = merge %trueResult_84 {handshake.bb = 9 : ui32, handshake.name = "merge11"} : <i32>
    %75 = merge %trueResult_86 {handshake.bb = 9 : ui32, handshake.name = "merge12"} : <i32>
    %76 = merge %trueResult_88 {handshake.bb = 9 : ui32, handshake.name = "merge13"} : <i32>
    %result_68, %index_69 = control_merge [%trueResult_90]  {handshake.bb = 9 : ui32, handshake.name = "control_merge8"} : [<>] to <>, <i1>
    %77 = source {handshake.bb = 9 : ui32, handshake.name = "source10"} : <>
    %78 = constant %77 {handshake.bb = 9 : ui32, handshake.name = "constant13", value = 0 : i32} : <>, <i32>
    %79 = cmpi slt, %75, %76 {handshake.bb = 9 : ui32, handshake.name = "cmpi9"} : <i32>
    %80 = select %79[%75, %76] {handshake.bb = 9 : ui32, handshake.name = "select0"} : <i1>, <i32>
    %81 = cmpi eq, %73, %78 {handshake.bb = 9 : ui32, handshake.name = "cmpi10"} : <i32>
    %trueResult_70, %falseResult_71 = cond_br %81, %80 {handshake.bb = 9 : ui32, handshake.name = "cond_br37"} : <i1>, <i32>
    %trueResult_72, %falseResult_73 = cond_br %81, %74 {handshake.bb = 9 : ui32, handshake.name = "cond_br38"} : <i1>, <i32>
    %trueResult_74, %falseResult_75 = cond_br %81, %result_68 {handshake.bb = 9 : ui32, handshake.name = "cond_br39"} : <i1>, <>
    %trueResult_76, %falseResult_77 = cond_br %81, %73 {handshake.bb = 9 : ui32, handshake.name = "cond_br40"} : <i1>, <i32>
    %82 = mux %index_79 [%falseResult_67, %falseResult_77] {handshake.bb = 10 : ui32, handshake.name = "mux12"} : <i1>, [<i32>, <i32>] to <i32>
    %83 = mux %index_79 [%falseResult_61, %falseResult_71] {handshake.bb = 10 : ui32, handshake.name = "mux13"} : <i1>, [<i32>, <i32>] to <i32>
    %84 = mux %index_79 [%falseResult_63, %falseResult_73] {handshake.bb = 10 : ui32, handshake.name = "mux14"} : <i1>, [<i32>, <i32>] to <i32>
    %result_78, %index_79 = control_merge [%falseResult_65, %falseResult_75]  {handshake.bb = 10 : ui32, handshake.name = "control_merge9"} : [<>, <>] to <>, <i1>
    %85 = source {handshake.bb = 10 : ui32, handshake.name = "source11"} : <>
    %86 = constant %85 {handshake.bb = 10 : ui32, handshake.name = "constant14", value = -1 : i32} : <>, <i32>
    %87 = source {handshake.bb = 10 : ui32, handshake.name = "source12"} : <>
    %88 = constant %87 {handshake.bb = 10 : ui32, handshake.name = "constant15", value = 0 : i32} : <>, <i32>
    %89 = subi %82, %83 {handshake.bb = 10 : ui32, handshake.name = "subi0"} : <i32>
    %90 = cmpi sgt, %89, %86 {handshake.bb = 10 : ui32, handshake.name = "cmpi11"} : <i32>
    %91 = subi %88, %89 {handshake.bb = 10 : ui32, handshake.name = "subi1"} : <i32>
    %92 = select %90[%89, %91] {handshake.bb = 10 : ui32, handshake.name = "select1"} : <i1>, <i32>
    %93 = br %92 {handshake.bb = 10 : ui32, handshake.name = "br12"} : <i32>
    %94 = br %84 {handshake.bb = 10 : ui32, handshake.name = "br13"} : <i32>
    %95 = br %82 {handshake.bb = 10 : ui32, handshake.name = "br14"} : <i32>
    %96 = br %83 {handshake.bb = 10 : ui32, handshake.name = "br15"} : <i32>
    %97 = br %result_78 {handshake.bb = 10 : ui32, handshake.name = "br16"} : <>
    %98 = mux %index_81 [%93, %falseResult_93] {handshake.bb = 11 : ui32, handshake.name = "mux15"} : <i1>, [<i32>, <i32>] to <i32>
    %99 = mux %index_81 [%94, %falseResult_85] {handshake.bb = 11 : ui32, handshake.name = "mux16"} : <i1>, [<i32>, <i32>] to <i32>
    %100 = mux %index_81 [%95, %falseResult_87] {handshake.bb = 11 : ui32, handshake.name = "mux17"} : <i1>, [<i32>, <i32>] to <i32>
    %101 = mux %index_81 [%96, %falseResult_89] {handshake.bb = 11 : ui32, handshake.name = "mux18"} : <i1>, [<i32>, <i32>] to <i32>
    %result_80, %index_81 = control_merge [%97, %falseResult_91]  {handshake.bb = 11 : ui32, handshake.name = "control_merge10"} : [<>, <>] to <>, <i1>
    %102 = source {handshake.bb = 11 : ui32, handshake.name = "source13"} : <>
    %103 = constant %102 {handshake.bb = 11 : ui32, handshake.name = "constant16", value = 1 : i32} : <>, <i32>
    %104 = source {handshake.bb = 11 : ui32, handshake.name = "source14"} : <>
    %105 = constant %104 {handshake.bb = 11 : ui32, handshake.name = "constant17", value = 0 : i32} : <>, <i32>
    %106 = cmpi slt, %98, %103 {handshake.bb = 11 : ui32, handshake.name = "cmpi12"} : <i32>
    %107 = andi %98, %103 {handshake.bb = 11 : ui32, handshake.name = "andi4"} : <i32>
    %108 = cmpi ne, %107, %105 {handshake.bb = 11 : ui32, handshake.name = "cmpi13"} : <i32>
    %109 = ori %108, %106 {handshake.bb = 11 : ui32, handshake.name = "ori4"} : <i1>
    %110 = shrsi %98, %103 {handshake.bb = 11 : ui32, handshake.name = "shrsi4"} : <i32>
    %trueResult_82, %falseResult_83 = cond_br %109, %98 {handshake.bb = 11 : ui32, handshake.name = "cond_br41"} : <i1>, <i32>
    %trueResult_84, %falseResult_85 = cond_br %109, %99 {handshake.bb = 11 : ui32, handshake.name = "cond_br42"} : <i1>, <i32>
    %trueResult_86, %falseResult_87 = cond_br %109, %100 {handshake.bb = 11 : ui32, handshake.name = "cond_br43"} : <i1>, <i32>
    %trueResult_88, %falseResult_89 = cond_br %109, %101 {handshake.bb = 11 : ui32, handshake.name = "cond_br44"} : <i1>, <i32>
    %trueResult_90, %falseResult_91 = cond_br %109, %result_80 {handshake.bb = 11 : ui32, handshake.name = "cond_br45"} : <i1>, <>
    %trueResult_92, %falseResult_93 = cond_br %109, %110 {handshake.bb = 11 : ui32, handshake.name = "cond_br46"} : <i1>, <i32>
    %111 = mux %index_95 [%trueResult_60, %trueResult_70] {handshake.bb = 12 : ui32, handshake.name = "mux19"} : <i1>, [<i32>, <i32>] to <i32>
    %112 = mux %index_95 [%trueResult_62, %trueResult_72] {handshake.bb = 12 : ui32, handshake.name = "mux20"} : <i1>, [<i32>, <i32>] to <i32>
    %result_94, %index_95 = control_merge [%trueResult_64, %trueResult_74]  {handshake.bb = 12 : ui32, handshake.name = "control_merge11"} : [<>, <>] to <>, <i1>
    %113 = shli %111, %112 {handshake.bb = 12 : ui32, handshake.name = "shli0"} : <i32>
    %114 = br %113 {handshake.bb = 12 : ui32, handshake.name = "br17"} : <i32>
    %115 = br %result_94 {handshake.bb = 12 : ui32, handshake.name = "br18"} : <>
    %116 = mux %index_97 [%trueResult, %trueResult_4, %114] {handshake.bb = 13 : ui32, handshake.name = "mux21"} : <i2>, [<i32>, <i32>, <i32>] to <i32>
    %result_96, %index_97 = control_merge [%trueResult_0, %trueResult_6, %115]  {handshake.bb = 13 : ui32, handshake.name = "control_merge12"} : [<>, <>, <>] to <>, <i2>
    end {handshake.bb = 13 : ui32, handshake.name = "end0"} %116, %arg2 : <i32>, <>
  }
}

