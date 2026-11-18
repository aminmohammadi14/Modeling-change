# ورودی آزمون؛ هر اجرا فضای مستقل دارد و نام‌های Main دست‌نخورده باقی می‌مانند.
# خود بدنه در سطح بالای ماژول ارزیابی می‌شود، نه در let با world age قدیمی.
Base.include(Module(gensym(:REVCSDataTests)), joinpath(@__DIR__, "test_step01_body.jl"))
