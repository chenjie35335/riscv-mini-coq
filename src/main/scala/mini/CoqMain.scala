package mini

import chisel3.stage.{ChiselGeneratorAnnotation, ChiselStage}

/** Emit resolved high FIRRTL for the formal-verification CoreSoc wrapper. */
object CoqMain extends App {
  (new ChiselStage).execute(
    Array("-X", "high") ++ args,
    Seq(ChiselGeneratorAnnotation(() => new CoreSoc(new Core(MiniConfig().core))))
  )
}
DontCare