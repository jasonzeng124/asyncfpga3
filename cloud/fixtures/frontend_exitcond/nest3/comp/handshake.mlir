module {
  handshake.func @nest3(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["a", "b", "start"], resNames = ["out0", "end"]} {
    %0 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 0 : i32} : <>, <i32>
    %1 = constant %arg2 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 74565 : i32} : <>, <i32>
    %2 = cmpi sgt, %arg0, %0 {handshake.bb = 0 : ui32, handshake.name = "cmpi0"} : <i32>
    %trueResult, %falseResult = cond_br %2, %1 {handshake.bb = 0 : ui32, handshake.name = "cond_br6"} : <i1>, <i32>
    %trueResult_0, %falseResult_1 = cond_br %2, %0 {handshake.bb = 0 : ui32, handshake.name = "cond_br7"} : <i1>, <i32>
    %trueResult_2, %falseResult_3 = cond_br %2, %arg0 {handshake.bb = 0 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>
    %trueResult_4, %falseResult_5 = cond_br %2, %arg1 {handshake.bb = 0 : ui32, handshake.name = "cond_br9"} : <i1>, <i32>
    %trueResult_6, %falseResult_7 = cond_br %2, %arg2 {handshake.bb = 0 : ui32, handshake.name = "cond_br10"} : <i1>, <>
    %3 = mux %index [%trueResult, %trueResult_72] {handshake.bb = 1 : ui32, handshake.name = "mux0"} : <i1>, [<i32>, <i32>] to <i32>
    %4 = mux %index [%trueResult_0, %trueResult_74] {handshake.bb = 1 : ui32, handshake.name = "mux1"} : <i1>, [<i32>, <i32>] to <i32>
    %5 = mux %index [%trueResult_2, %trueResult_76] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>
    %6 = mux %index [%trueResult_4, %trueResult_78] {handshake.bb = 1 : ui32, handshake.name = "mux3"} : <i1>, [<i32>, <i32>] to <i32>
    %result, %index = control_merge [%trueResult_6, %trueResult_80]  {handshake.bb = 1 : ui32, handshake.name = "control_merge0"} : [<>, <>] to <>, <i1>
    %7 = constant %result {handshake.bb = 1 : ui32, handshake.name = "constant7", value = 0 : i32} : <>, <i32>
    %8 = cmpi sgt, %6, %7 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>
    %trueResult_8, %falseResult_9 = cond_br %8, %7 {handshake.bb = 1 : ui32, handshake.name = "cond_br11"} : <i1>, <i32>
    %trueResult_10, %falseResult_11 = cond_br %8, %3 {handshake.bb = 1 : ui32, handshake.name = "cond_br12"} : <i1>, <i32>
    %trueResult_12, %falseResult_13 = cond_br %8, %5 {handshake.bb = 1 : ui32, handshake.name = "cond_br13"} : <i1>, <i32>
    %trueResult_14, %falseResult_15 = cond_br %8, %6 {handshake.bb = 1 : ui32, handshake.name = "cond_br14"} : <i1>, <i32>
    %trueResult_16, %falseResult_17 = cond_br %8, %4 {handshake.bb = 1 : ui32, handshake.name = "cond_br15"} : <i1>, <i32>
    %trueResult_18, %falseResult_19 = cond_br %8, %result {handshake.bb = 1 : ui32, handshake.name = "cond_br16"} : <i1>, <>
    %9 = mux %index_21 [%trueResult_8, %trueResult_58] {handshake.bb = 2 : ui32, handshake.name = "mux4"} : <i1>, [<i32>, <i32>] to <i32>
    %10 = mux %index_21 [%trueResult_10, %trueResult_60] {handshake.bb = 2 : ui32, handshake.name = "mux5"} : <i1>, [<i32>, <i32>] to <i32>
    %11 = mux %index_21 [%trueResult_12, %trueResult_62] {handshake.bb = 2 : ui32, handshake.name = "mux6"} : <i1>, [<i32>, <i32>] to <i32>
    %12 = mux %index_21 [%trueResult_14, %trueResult_64] {handshake.bb = 2 : ui32, handshake.name = "mux7"} : <i1>, [<i32>, <i32>] to <i32>
    %13 = mux %index_21 [%trueResult_16, %trueResult_66] {handshake.bb = 2 : ui32, handshake.name = "mux8"} : <i1>, [<i32>, <i32>] to <i32>
    %result_20, %index_21 = control_merge [%trueResult_18, %trueResult_68]  {handshake.bb = 2 : ui32, handshake.name = "control_merge1"} : [<>, <>] to <>, <i1>
    %14 = source {handshake.bb = 2 : ui32, handshake.name = "source0"} : <>
    %15 = constant %14 {handshake.bb = 2 : ui32, handshake.name = "constant8", value = 3 : i32} : <>, <i32>
    %16 = constant %result_20 {handshake.bb = 2 : ui32, handshake.name = "constant9", value = 0 : i32} : <>, <i32>
    %17 = xori %13, %9 {handshake.bb = 2 : ui32, handshake.name = "xori0"} : <i32>
    %18 = andi %17, %15 {handshake.bb = 2 : ui32, handshake.name = "andi0"} : <i32>
    %19 = cmpi ugt, %18, %16 {handshake.bb = 2 : ui32, handshake.name = "cmpi2"} : <i32>
    %trueResult_22, %falseResult_23 = cond_br %19, %16 {handshake.bb = 2 : ui32, handshake.name = "cond_br17"} : <i1>, <i32>
    %trueResult_24, %falseResult_25 = cond_br %19, %10 {handshake.bb = 2 : ui32, handshake.name = "cond_br18"} : <i1>, <i32>
    %trueResult_26, %falseResult_27 = cond_br %19, %11 {handshake.bb = 2 : ui32, handshake.name = "cond_br19"} : <i1>, <i32>
    %trueResult_28, %falseResult_29 = cond_br %19, %12 {handshake.bb = 2 : ui32, handshake.name = "cond_br20"} : <i1>, <i32>
    %trueResult_30, %falseResult_31 = cond_br %19, %13 {handshake.bb = 2 : ui32, handshake.name = "cond_br21"} : <i1>, <i32>
    %trueResult_32, %falseResult_33 = cond_br %19, %9 {handshake.bb = 2 : ui32, handshake.name = "cond_br22"} : <i1>, <i32>
    %trueResult_34, %falseResult_35 = cond_br %19, %18 {handshake.bb = 2 : ui32, handshake.name = "cond_br23"} : <i1>, <i32>
    %trueResult_36, %falseResult_37 = cond_br %19, %result_20 {handshake.bb = 2 : ui32, handshake.name = "cond_br24"} : <i1>, <>
    %20 = mux %index_39 [%trueResult_22, %trueResult_40] {handshake.bb = 3 : ui32, handshake.name = "mux9"} : <i1>, [<i32>, <i32>] to <i32>
    %21 = mux %index_39 [%trueResult_24, %trueResult_42] {handshake.bb = 3 : ui32, handshake.name = "mux10"} : <i1>, [<i32>, <i32>] to <i32>
    %22 = mux %index_39 [%trueResult_26, %trueResult_44] {handshake.bb = 3 : ui32, handshake.name = "mux11"} : <i1>, [<i32>, <i32>] to <i32>
    %23 = mux %index_39 [%trueResult_28, %trueResult_46] {handshake.bb = 3 : ui32, handshake.name = "mux12"} : <i1>, [<i32>, <i32>] to <i32>
    %24 = mux %index_39 [%trueResult_30, %trueResult_48] {handshake.bb = 3 : ui32, handshake.name = "mux13"} : <i1>, [<i32>, <i32>] to <i32>
    %25 = mux %index_39 [%trueResult_32, %trueResult_50] {handshake.bb = 3 : ui32, handshake.name = "mux14"} : <i1>, [<i32>, <i32>] to <i32>
    %26 = mux %index_39 [%trueResult_34, %trueResult_52] {handshake.bb = 3 : ui32, handshake.name = "mux15"} : <i1>, [<i32>, <i32>] to <i32>
    %result_38, %index_39 = control_merge [%trueResult_36, %trueResult_54]  {handshake.bb = 3 : ui32, handshake.name = "control_merge2"} : [<>, <>] to <>, <i1>
    %27 = source {handshake.bb = 3 : ui32, handshake.name = "source1"} : <>
    %28 = constant %27 {handshake.bb = 3 : ui32, handshake.name = "constant10", value = 1 : i32} : <>, <i32>
    %29 = source {handshake.bb = 3 : ui32, handshake.name = "source2"} : <>
    %30 = constant %29 {handshake.bb = 3 : ui32, handshake.name = "constant11", value = 2 : i32} : <>, <i32>
    %31 = source {handshake.bb = 3 : ui32, handshake.name = "source3"} : <>
    %32 = constant %31 {handshake.bb = 3 : ui32, handshake.name = "constant12", value = 4 : i32} : <>, <i32>
    %33 = source {handshake.bb = 3 : ui32, handshake.name = "source4"} : <>
    %34 = constant %33 {handshake.bb = 3 : ui32, handshake.name = "constant13", value = 5 : i32} : <>, <i32>
    %35 = shrui %21, %34 {handshake.bb = 3 : ui32, handshake.name = "shrui0"} : <i32>
    %36 = xori %21, %35 {handshake.bb = 3 : ui32, handshake.name = "xori1"} : <i32>
    %37 = shli %24, %32 {handshake.bb = 3 : ui32, handshake.name = "shli0"} : <i32>
    %38 = shli %25, %30 {handshake.bb = 3 : ui32, handshake.name = "shli1"} : <i32>
    %39 = xori %37, %38 {handshake.bb = 3 : ui32, handshake.name = "xori2"} : <i32>
    %40 = xori %39, %20 {handshake.bb = 3 : ui32, handshake.name = "xori3"} : <i32>
    %41 = addi %36, %40 {handshake.bb = 3 : ui32, handshake.name = "addi0"} : <i32>
    %42 = addi %41, %28 {handshake.bb = 3 : ui32, handshake.name = "addi1"} : <i32>
    %43 = addi %20, %28 {handshake.bb = 3 : ui32, handshake.name = "addi2"} : <i32>
    %44 = cmpi ne, %43, %26 {handshake.bb = 3 : ui32, handshake.name = "cmpi3"} : <i32>
    %trueResult_40, %falseResult_41 = cond_br %44, %43 {handshake.bb = 3 : ui32, handshake.name = "cond_br25"} : <i1>, <i32>
    %trueResult_42, %falseResult_43 = cond_br %44, %42 {handshake.bb = 3 : ui32, handshake.name = "cond_br26"} : <i1>, <i32>
    %trueResult_44, %falseResult_45 = cond_br %44, %22 {handshake.bb = 3 : ui32, handshake.name = "cond_br27"} : <i1>, <i32>
    %trueResult_46, %falseResult_47 = cond_br %44, %23 {handshake.bb = 3 : ui32, handshake.name = "cond_br28"} : <i1>, <i32>
    %trueResult_48, %falseResult_49 = cond_br %44, %24 {handshake.bb = 3 : ui32, handshake.name = "cond_br29"} : <i1>, <i32>
    %trueResult_50, %falseResult_51 = cond_br %44, %25 {handshake.bb = 3 : ui32, handshake.name = "cond_br30"} : <i1>, <i32>
    %trueResult_52, %falseResult_53 = cond_br %44, %26 {handshake.bb = 3 : ui32, handshake.name = "cond_br31"} : <i1>, <i32>
    %trueResult_54, %falseResult_55 = cond_br %44, %result_38 {handshake.bb = 3 : ui32, handshake.name = "cond_br32"} : <i1>, <>
    %45 = mux %index_57 [%falseResult_25, %falseResult_43] {handshake.bb = 4 : ui32, handshake.name = "mux16"} : <i1>, [<i32>, <i32>] to <i32>
    %46 = mux %index_57 [%falseResult_27, %falseResult_45] {handshake.bb = 4 : ui32, handshake.name = "mux17"} : <i1>, [<i32>, <i32>] to <i32>
    %47 = mux %index_57 [%falseResult_29, %falseResult_47] {handshake.bb = 4 : ui32, handshake.name = "mux18"} : <i1>, [<i32>, <i32>] to <i32>
    %48 = mux %index_57 [%falseResult_31, %falseResult_49] {handshake.bb = 4 : ui32, handshake.name = "mux19"} : <i1>, [<i32>, <i32>] to <i32>
    %49 = mux %index_57 [%falseResult_33, %falseResult_51] {handshake.bb = 4 : ui32, handshake.name = "mux20"} : <i1>, [<i32>, <i32>] to <i32>
    %result_56, %index_57 = control_merge [%falseResult_37, %falseResult_55]  {handshake.bb = 4 : ui32, handshake.name = "control_merge3"} : [<>, <>] to <>, <i1>
    %50 = source {handshake.bb = 4 : ui32, handshake.name = "source5"} : <>
    %51 = constant %50 {handshake.bb = 4 : ui32, handshake.name = "constant14", value = 1 : i32} : <>, <i32>
    %52 = addi %49, %51 {handshake.bb = 4 : ui32, handshake.name = "addi3"} : <i32>
    %53 = cmpi ne, %52, %47 {handshake.bb = 4 : ui32, handshake.name = "cmpi4"} : <i32>
    %trueResult_58, %falseResult_59 = cond_br %53, %52 {handshake.bb = 4 : ui32, handshake.name = "cond_br33"} : <i1>, <i32>
    %trueResult_60, %falseResult_61 = cond_br %53, %45 {handshake.bb = 4 : ui32, handshake.name = "cond_br34"} : <i1>, <i32>
    %trueResult_62, %falseResult_63 = cond_br %53, %46 {handshake.bb = 4 : ui32, handshake.name = "cond_br35"} : <i1>, <i32>
    %trueResult_64, %falseResult_65 = cond_br %53, %47 {handshake.bb = 4 : ui32, handshake.name = "cond_br36"} : <i1>, <i32>
    %trueResult_66, %falseResult_67 = cond_br %53, %48 {handshake.bb = 4 : ui32, handshake.name = "cond_br37"} : <i1>, <i32>
    %trueResult_68, %falseResult_69 = cond_br %53, %result_56 {handshake.bb = 4 : ui32, handshake.name = "cond_br38"} : <i1>, <>
    %54 = mux %index_71 [%falseResult_11, %falseResult_61] {handshake.bb = 5 : ui32, handshake.name = "mux21"} : <i1>, [<i32>, <i32>] to <i32>
    %55 = mux %index_71 [%falseResult_13, %falseResult_63] {handshake.bb = 5 : ui32, handshake.name = "mux22"} : <i1>, [<i32>, <i32>] to <i32>
    %56 = mux %index_71 [%falseResult_15, %falseResult_65] {handshake.bb = 5 : ui32, handshake.name = "mux23"} : <i1>, [<i32>, <i32>] to <i32>
    %57 = mux %index_71 [%falseResult_17, %falseResult_67] {handshake.bb = 5 : ui32, handshake.name = "mux24"} : <i1>, [<i32>, <i32>] to <i32>
    %result_70, %index_71 = control_merge [%falseResult_19, %falseResult_69]  {handshake.bb = 5 : ui32, handshake.name = "control_merge4"} : [<>, <>] to <>, <i1>
    %58 = source {handshake.bb = 5 : ui32, handshake.name = "source6"} : <>
    %59 = constant %58 {handshake.bb = 5 : ui32, handshake.name = "constant15", value = 1 : i32} : <>, <i32>
    %60 = addi %57, %59 {handshake.bb = 5 : ui32, handshake.name = "addi4"} : <i32>
    %61 = cmpi ne, %60, %55 {handshake.bb = 5 : ui32, handshake.name = "cmpi5"} : <i32>
    %trueResult_72, %falseResult_73 = cond_br %61, %54 {handshake.bb = 5 : ui32, handshake.name = "cond_br39"} : <i1>, <i32>
    %trueResult_74, %falseResult_75 = cond_br %61, %60 {handshake.bb = 5 : ui32, handshake.name = "cond_br40"} : <i1>, <i32>
    %trueResult_76, %falseResult_77 = cond_br %61, %55 {handshake.bb = 5 : ui32, handshake.name = "cond_br41"} : <i1>, <i32>
    %trueResult_78, %falseResult_79 = cond_br %61, %56 {handshake.bb = 5 : ui32, handshake.name = "cond_br42"} : <i1>, <i32>
    %trueResult_80, %falseResult_81 = cond_br %61, %result_70 {handshake.bb = 5 : ui32, handshake.name = "cond_br43"} : <i1>, <>
    %62 = mux %index_83 [%falseResult, %falseResult_73] {handshake.bb = 6 : ui32, handshake.name = "mux25"} : <i1>, [<i32>, <i32>] to <i32>
    %result_82, %index_83 = control_merge [%falseResult_7, %falseResult_81]  {handshake.bb = 6 : ui32, handshake.name = "control_merge5"} : [<>, <>] to <>, <i1>
    end {handshake.bb = 6 : ui32, handshake.name = "end0"} %62, %arg2 : <i32>, <>
  }
}

