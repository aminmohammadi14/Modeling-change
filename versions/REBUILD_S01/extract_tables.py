"""استخراج قابل تکرار جدول‌های ۱ تا ۱۱؛ فقط بخش ۳۳ باس، بدون تولید داده."""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path


def extract(pdf):
    # استخراج متن با حفظ ستون‌ها؛ جدول‌های سیستم ۵۴ باس هرگز وارد این مرحله نمی‌شوند.
    text = subprocess.check_output(['pdftotext', '-layout', str(pdf), '-']).decode()
    text = text.split('Case: 54-bus')[0]
    pieces = re.split(r'Table (\d+)\.', text)
    sections = {int(pieces[i]): pieces[i+1] for i in range(1, len(pieces), 2)}
    if set(sections) != set(range(1, 12)):
        raise ValueError('جدول‌های مورد انتظار ۱ تا ۱۱ یافت نشدند')
    tables = {}
    # انتخاب فقط سطر کامل عددی؛ هیچ گردکردن، درون‌یابی یا پرکردن مقدار مفقود انجام نمی‌شود.
    for number in (2, 3, 4, 5, 6, 8, 11):
        rows = []
        width = {2: 10, 3: 5, 4: 3, 5: 5, 6: 3, 8: 5, 11: 5}[number]
        for line in sections[number].splitlines():
            line = line.strip().rstrip('\\') # علامت زائد چاپی پس از 197.50 در جدول ۴
            if re.fullmatch(r'\d+(?:\.\d+)?(?:\s+\d+(?:\.\d+)?)+', line):
                row = line.split()
                if len(row) != width:
                    raise ValueError(f'تعداد ستون غیرمنتظره: جدول {number}: {line}')
                rows.append([float(x) if '.' in x else int(x) for x in row])
        tables[number] = rows
    tables[1] = [[int(a), float(b), float(c), d == 'Yes'] for a,b,c,d in
                 re.findall(r'^\s*R(\d+)\s+(\d+\.\d+)\s+(\d+(?:\.\d+)?)\s+(Yes|No)\s*$', sections[1], re.M)]
    # جدول‌های کوتاه بر اساس سطر کامل خوانده می‌شوند، نه اعداد ثابت در برنامه.
    tables[7] = [[float(x) for x in row.split()] for row in sections[7].splitlines()
                 if re.fullmatch(r'\s*\d+\.\d+\s+\d+\.\d+\s+\d+\.\d+\s*', row)]
    tables[9] = []
    for line in sections[9].splitlines():
        m = re.match(r'^\s*(FCS|BESS|Onsite PV)\s+(.+)$', line)
        if m:
            # علامت / عیناً به معنی «مقدار ارائه نشده/نامرتبط» حفظ می‌شود؛ صفر جایگزین نیست.
            cells = m[2].split()
            tables[9].append([m[1]] + [x if x == '/' else float(x) for x in cells])
    tables[10] = [[float(x) for x in row.split()] for row in sections[10].splitlines()
                  if re.fullmatch(r'\s*\d+(?:\.\d+)?(?:\s+\d+(?:\.\d+)?){7}\s*', row)]
    expected = {1:20,2:24,3:24,4:5,5:24,6:5,7:1,8:24,9:3,10:1,11:37}
    for n,count in expected.items():
        if len(tables[n]) != count:
            raise ValueError(f'جدول {n}: انتظار {count} سطر، استخراج {len(tables[n])}')
    return tables


# ستون‌ها و واحدهای چاپ‌شده بخشی از قرارداد خواندن منبع هستند، نه پارامترهای مدل.
SCHEMA = {
 1: ([1], ['road','capacity','free_time_min','existing_revcs'], ['id','not_printed','min','boolean']),
 2: ([2], ['hour','T1_T6','T1_T10','T1_T12','T3_T6','T3_T12','T3_T11','T4_T9','T4_T10','T4_T12'], ['hour']+['traffic_flow_unit_not_printed']*9),
 3: ([2], ['hour','day1','day2','day3','day4'], ['hour']+['p.u.']*4),
 4: ([2], ['id','bus','capacity'], ['id','id','kW']),
 5: ([3], ['hour','day1','day2','day3','day4'], ['hour']+['p.u.']*4),
 6: ([3], ['id','bus','capacity'], ['id','id','kW']),
 7: ([3], ['FCS','BESS','onsite_PV'], ['kW','kW_as_printed','kW']),
 8: ([3,4], ['hour','day1','day2','day3','day4'], ['hour']+['not_printed_in_table']*4),
 9: ([4], ['device','upper','lower','ramp','charge_efficiency','discharge_efficiency'], ['name','kW','kW','kWh_as_printed','ratio','ratio']),
 10: ([4], ['Pbu_upper','V_upper','V_lower','V_hat','tan_phi','Sw','reactive_factor','gamma1_gamma2'], ['kW','not_printed','not_printed','not_printed','ratio','not_printed','ratio','ratio']),
 11: ([4], ['from_bus','to_bus','r','x','active_capacity'], ['id','id','not_printed','not_printed','kW']),
}


def dump(tables, pdf):
    lines = ['# داده‌های چاپ‌شده؛ ابهام واحدها در ISSUES_FA.md ثبت شده است.',
             'source_id = "supplement"', f'source_sha256 = "{hashlib.sha256(pdf.read_bytes()).hexdigest()}"']
    for n in sorted(tables):
        pages, columns, units = SCHEMA[n]
        lines += [f'\n[table{n}]', f'pages = {json.dumps(pages)}',
                  f'columns = {json.dumps(columns)}', f'units_as_printed = {json.dumps(units)}', 'rows = [']
        lines += ['  '+json.dumps(row)+',' for row in tables[n]]
        lines += [']']
    return '\n'.join(lines)+'\n'


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('pdf', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    args.output.write_text(dump(extract(args.pdf), args.pdf), encoding='utf-8')
