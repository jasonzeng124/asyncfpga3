module {
  func.func @video_filter(%arg0: i32 {handshake.arg_name = "offset"}, %arg1: i32 {handshake.arg_name = "scale"}, %arg2: memref<900xi32> {handshake.arg_name = "pixelR"}, %arg3: memref<900xi32> {handshake.arg_name = "pixelG"}, %arg4: memref<900xi32> {handshake.arg_name = "pixelB"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %c0_i32_0 = arith.constant {handshake.name = "constant9"} 0 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    %3 = arith.extui %0 {handshake.name = "extui2"} : i32 to i64
    %4 = arith.extui %0 {handshake.name = "extui3"} : i32 to i64
    %5 = arith.extui %0 {handshake.name = "extui4"} : i32 to i64
    %6 = arith.extui %0 {handshake.name = "extui5"} : i32 to i64
    cf.br ^bb2(%c0_i32_0 : i32) {handshake.name = "br1"}
  ^bb2(%7: i32):  // 2 preds: ^bb1, ^bb2
    %c30_i32 = arith.constant {handshake.name = "constant10"} 30 : i32
    %c1_i32 = arith.constant {handshake.name = "constant11"} 1 : i32
    %c4_i32 = arith.constant {handshake.name = "constant12"} 4 : i32
    %c4_i64 = arith.constant {handshake.name = "constant13"} 4 : i64
    %c3_i64 = arith.constant {handshake.name = "constant14"} 3 : i64
    %c2_i64 = arith.constant {handshake.name = "constant15"} 2 : i64
    %c1_i64 = arith.constant {handshake.name = "constant16"} 1 : i64
    %8 = arith.extui %7 {handshake.name = "extui6"} : i32 to i64
    %9 = arith.shli %1, %c1_i64 {handshake.name = "shli0"} : i64
    %10 = arith.shli %1, %c2_i64 {handshake.name = "shli1"} : i64
    %11 = arith.addi %9, %10 {handshake.name = "addi8"} : i64
    %12 = arith.shli %1, %c3_i64 {handshake.name = "shli2"} : i64
    %13 = arith.shli %1, %c4_i64 {handshake.name = "shli3"} : i64
    %14 = arith.addi %12, %13 {handshake.name = "addi9"} : i64
    %15 = arith.addi %11, %14 {handshake.name = "addi10"} : i64
    %16 = arith.addi %15, %8 {handshake.name = "addi0"} : i64
    %17 = arith.index_cast %16 {handshake.name = "index_cast0"} : i64 to index
    %18 = memref.load %arg2[%17] {handshake.name = "load0"} : memref<900xi32>
    %19 = arith.subi %18, %arg0 {handshake.name = "subi0"} : i32
    %20 = arith.muli %19, %arg1 {handshake.name = "muli1"} : i32
    %21 = arith.shrsi %20, %c4_i32 {handshake.name = "shrsi0"} : i32
    %22 = arith.extui %7 {handshake.name = "extui7"} : i32 to i64
    %23 = arith.shli %2, %c1_i64 {handshake.name = "shli4"} : i64
    %24 = arith.shli %2, %c2_i64 {handshake.name = "shli5"} : i64
    %25 = arith.addi %23, %24 {handshake.name = "addi11"} : i64
    %26 = arith.shli %2, %c3_i64 {handshake.name = "shli6"} : i64
    %27 = arith.shli %2, %c4_i64 {handshake.name = "shli7"} : i64
    %28 = arith.addi %26, %27 {handshake.name = "addi12"} : i64
    %29 = arith.addi %25, %28 {handshake.name = "addi13"} : i64
    %30 = arith.addi %29, %22 {handshake.name = "addi1"} : i64
    %31 = arith.index_cast %30 {handshake.name = "index_cast1"} : i64 to index
    memref.store %21, %arg2[%31] {handshake.name = "store1"} : memref<900xi32>
    %32 = arith.extui %7 {handshake.name = "extui8"} : i32 to i64
    %33 = arith.shli %3, %c1_i64 {handshake.name = "shli8"} : i64
    %34 = arith.shli %3, %c2_i64 {handshake.name = "shli9"} : i64
    %35 = arith.addi %33, %34 {handshake.name = "addi14"} : i64
    %36 = arith.shli %3, %c3_i64 {handshake.name = "shli10"} : i64
    %37 = arith.shli %3, %c4_i64 {handshake.name = "shli11"} : i64
    %38 = arith.addi %36, %37 {handshake.name = "addi15"} : i64
    %39 = arith.addi %35, %38 {handshake.name = "addi16"} : i64
    %40 = arith.addi %39, %32 {handshake.name = "addi2"} : i64
    %41 = arith.index_cast %40 {handshake.name = "index_cast2"} : i64 to index
    %42 = memref.load %arg4[%41] {handshake.name = "load2"} : memref<900xi32>
    %43 = arith.subi %42, %arg0 {handshake.name = "subi1"} : i32
    %44 = arith.muli %43, %arg1 {handshake.name = "muli4"} : i32
    %45 = arith.shrsi %44, %c4_i32 {handshake.name = "shrsi1"} : i32
    %46 = arith.extui %7 {handshake.name = "extui9"} : i32 to i64
    %47 = arith.shli %4, %c1_i64 {handshake.name = "shli12"} : i64
    %48 = arith.shli %4, %c2_i64 {handshake.name = "shli13"} : i64
    %49 = arith.addi %47, %48 {handshake.name = "addi17"} : i64
    %50 = arith.shli %4, %c3_i64 {handshake.name = "shli14"} : i64
    %51 = arith.shli %4, %c4_i64 {handshake.name = "shli15"} : i64
    %52 = arith.addi %50, %51 {handshake.name = "addi18"} : i64
    %53 = arith.addi %49, %52 {handshake.name = "addi19"} : i64
    %54 = arith.addi %53, %46 {handshake.name = "addi3"} : i64
    %55 = arith.index_cast %54 {handshake.name = "index_cast3"} : i64 to index
    memref.store %45, %arg4[%55] {handshake.name = "store3"} : memref<900xi32>
    %56 = arith.extui %7 {handshake.name = "extui10"} : i32 to i64
    %57 = arith.shli %5, %c1_i64 {handshake.name = "shli16"} : i64
    %58 = arith.shli %5, %c2_i64 {handshake.name = "shli17"} : i64
    %59 = arith.addi %57, %58 {handshake.name = "addi20"} : i64
    %60 = arith.shli %5, %c3_i64 {handshake.name = "shli18"} : i64
    %61 = arith.shli %5, %c4_i64 {handshake.name = "shli19"} : i64
    %62 = arith.addi %60, %61 {handshake.name = "addi21"} : i64
    %63 = arith.addi %59, %62 {handshake.name = "addi22"} : i64
    %64 = arith.addi %63, %56 {handshake.name = "addi4"} : i64
    %65 = arith.index_cast %64 {handshake.name = "index_cast4"} : i64 to index
    %66 = memref.load %arg3[%65] {handshake.name = "load4"} : memref<900xi32>
    %67 = arith.subi %66, %arg0 {handshake.name = "subi2"} : i32
    %68 = arith.muli %67, %arg1 {handshake.name = "muli7"} : i32
    %69 = arith.shrsi %68, %c4_i32 {handshake.name = "shrsi2"} : i32
    %70 = arith.extui %7 {handshake.name = "extui11"} : i32 to i64
    %71 = arith.shli %6, %c1_i64 {handshake.name = "shli20"} : i64
    %72 = arith.shli %6, %c2_i64 {handshake.name = "shli21"} : i64
    %73 = arith.addi %71, %72 {handshake.name = "addi23"} : i64
    %74 = arith.shli %6, %c3_i64 {handshake.name = "shli22"} : i64
    %75 = arith.shli %6, %c4_i64 {handshake.name = "shli23"} : i64
    %76 = arith.addi %74, %75 {handshake.name = "addi24"} : i64
    %77 = arith.addi %73, %76 {handshake.name = "addi25"} : i64
    %78 = arith.addi %77, %70 {handshake.name = "addi5"} : i64
    %79 = arith.index_cast %78 {handshake.name = "index_cast5"} : i64 to index
    memref.store %69, %arg3[%79] {handshake.name = "store5"} : memref<900xi32>
    %80 = arith.addi %7, %c1_i32 {handshake.name = "addi6"} : i32
    %81 = arith.cmpi ult, %80, %c30_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %81, ^bb2(%80 : i32), ^bb3 {handshake.name = "cond_br0"}
  ^bb3:  // pred: ^bb2
    %c30_i32_1 = arith.constant {handshake.name = "constant17"} 30 : i32
    %c1_i32_2 = arith.constant {handshake.name = "constant18"} 1 : i32
    %82 = arith.addi %0, %c1_i32_2 {handshake.name = "addi7"} : i32
    %83 = arith.cmpi ult, %82, %c30_i32_1 {handshake.name = "cmpi1"} : i32
    cf.cond_br %83, ^bb1(%82 : i32), ^bb4 {handshake.name = "cond_br1"}
  ^bb4:  // pred: ^bb3
    return {handshake.name = "return0"}
  }
}

