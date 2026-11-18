# مسیر جاری: اصلاح گام‌به‌گام فایل ارسالی کاربر

مبنای ادامه، `CODE REFRENCE.jl` ارسالی کاربر است. نسخهٔ اصلی در گزارش CHG-0007 محفوظ است.

- [فایل کامل اصلاح اول: CODE_REFERENCE.jl](versions/REFERENCE_S01/CODE_REFERENCE.jl)
- [ZIP شامل فقط فایل اجرایی](versions/REFERENCE_S01/REFERENCE_S01_SINGLEFILE.zip)
- [تغییرات و مراحل بعد](versions/REFERENCE_S01/README_FA.md)
- [گزارش دائمی](REUSE.md)

```powershell
julia CODE_REFERENCE.jl
```

این نسخه گام اول داده است. خروجی در results_REFERENCE_S01 ساخته می‌شود.

---

# REVCS — 33P–12U

کد برنامه‌ریزی ایستگاه‌های شارژ برای شبکهٔ ۳۳ باس برق و ۱۲ گرهٔ حمل‌ونقل.

## اجرای ساده با یک فایل

فقط [revcs_step01_integrated.jl](versions/REBUILD_S01/revcs_step01_integrated.jl) را دریافت و اجرا کنید؛ پوشهٔ داده یا آزمون همراه لازم نیست. [ZIP شامل فقط همین یک فایل](versions/REBUILD_S01/REVCS_S01_SINGLEFILE.zip).

```powershell
julia revcs_step01_integrated.jl
```

خروجی در results_S01 کنار فایل ساخته می‌شود. این گام بررسی داده است و هنوز حل بهینه‌سازی نیست.

## بازنویسی مرحله‌به‌مرحله — S01

- [راهنمای گام اول](versions/REBUILD_S01/README_FA.md)
- [کد کامل گام اول با توضیحات فارسی](versions/REBUILD_S01/run_step01.jl)
- [دانلود ZIP گام اول](versions/REBUILD_S01/REBUILD_S01_complete.zip)
- [ابهام‌های داده و مدل](versions/REBUILD_S01/ISSUES_FA.md)
- [نقشهٔ شکل‌های مقاله](versions/REBUILD_S01/FIGURES_FA.md)

این گام داده‌های منبع را می‌خواند، کنترل می‌کند و نمودار ورودی می‌سازد؛ هنوز مدل بهینه‌سازی نیست. گزارش هر تغییر در REUSE.md ثبت می‌شود.

## سابقهٔ نسخهٔ ۱۹


- [دفتر ثابت گزارش‌ها، پرسش‌ها و تغییرات](REUSE.md)
- [کد کامل نسخهٔ ۱۹](versions/REVCS19/revcs_planning19.jl)
- [راهنمای نصب و اجرا](versions/REVCS19/README_FA.md)
- [ZIP کامل نسخهٔ ۱۹](versions/REVCS19/REVCS19_complete.zip)
- [پایپ‌لاین و بسته‌های قابل دانلود](https://github.com/aminmohammadi14/Modeling-change/actions/workflows/revcs.yml)

برای دانلود مستقیم ZIP، لینک بالا را باز و Download raw file را انتخاب کنید. برای دریافت بستهٔ جدید پایپ‌لاین، آخرین اجرای شاخهٔ موردنظر در Actions را باز کنید و artifact با پیشوند `REVCS-source-` را بگیرید؛ دانلود artifact نیازمند ورود به GitHub است. بستهٔ پایپ‌لاین شامل نسخهٔ کامل، گزارش‌ها، checksum و اطلاعات commit است. خروجی آزمون Julia با پیشوند `REVCS-validation-` جدا موجود می‌شود.

هر تغییر شمارهٔ `CHG-xxxx`، commit مشخص و ورودی جدید در `REUSE.md` دارد. آخرین کد تأییدشدهٔ موجود در این انتقال REVCS19 است؛ تطابق کامل با مقاله و حل مقاوم کل افق اثبات نشده‌اند. شرح محدودیت‌ها در گزارش محفوظ است.
