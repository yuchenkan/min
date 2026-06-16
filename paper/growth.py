"""Generate proof growth chart for the paper."""
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.dates as mdates
from datetime import datetime

# Python era (src/theorems/*.py)
py_data = [
    ('2026-04-27', 18418),
    ('2026-04-28', 18237),
    ('2026-04-29', 19758),
    ('2026-04-30', 20140),
    ('2026-05-03', 19652),
    ('2026-05-04', 19768),
    ('2026-05-05', 19784),
    ('2026-05-06', 19346),
    ('2026-05-07', 19948),
    ('2026-05-10', 22258),
    ('2026-05-11', 27055),
    ('2026-05-12', 33458),
    ('2026-05-13', 34947),
    ('2026-05-14', 36121),
    ('2026-05-15', 35841),
    ('2026-05-16', 39605),
    ('2026-05-17', 39059),
]

# DSL era (poc4/theorems/*.min) — rewrite from Python to C kernel + .min DSL
dsl_data = [
    ('2026-05-29', 2356),
    ('2026-05-30', 5119),
    ('2026-05-31', 9138),
    ('2026-06-01', 11957),
    ('2026-06-02', 16071),
    ('2026-06-03', 17639),
    ('2026-06-04', 18510),
    ('2026-06-05', 19901),
    ('2026-06-06', 21426),
    ('2026-06-12', 26477),
    ('2026-06-13', 33967),
    ('2026-06-15', 36686),
    ('2026-06-16', 38159),
]

fig, ax = plt.subplots(figsize=(6, 3.5))

py_dates = [datetime.strptime(d, '%Y-%m-%d') for d, _ in py_data]
py_lines = [l for _, l in py_data]
ax.plot(py_dates, [l/1000 for l in py_lines], 'k-o', markersize=3, linewidth=1, label='Python prototype')

dsl_dates = [datetime.strptime(d, '%Y-%m-%d') for d, _ in dsl_data]
dsl_lines = [l for _, l in dsl_data]
ax.plot(dsl_dates, [l/1000 for l in dsl_lines], 'b-s', markersize=3, linewidth=1, label='.min DSL (C kernel)')

# Annotations
ax.annotate('recursion theorem', xy=(datetime(2026, 5, 10), 22.3),
            xytext=(datetime(2026, 4, 28), 28),
            arrowprops=dict(arrowstyle='->', color='gray'),
            fontsize=7, color='gray')
ax.annotate('TM correctness\n(Python)', xy=(datetime(2026, 5, 16), 39.6),
            xytext=(datetime(2026, 5, 8), 44),
            arrowprops=dict(arrowstyle='->', color='gray'),
            fontsize=7, color='gray')
ax.annotate('rewrite to\nC + DSL', xy=(datetime(2026, 5, 29), 2.4),
            xytext=(datetime(2026, 5, 20), 8),
            arrowprops=dict(arrowstyle='->', color='gray'),
            fontsize=7, color='gray')
ax.annotate('TM correctness\n(DSL)', xy=(datetime(2026, 6, 16), 38.2),
            xytext=(datetime(2026, 6, 7), 42),
            arrowprops=dict(arrowstyle='->', color='gray'),
            fontsize=7, color='gray')

ax.set_ylabel('Lines of proof code (thousands)', fontsize=9)
ax.set_ylim(0, 48)
ax.xaxis.set_major_formatter(mdates.DateFormatter('%b %d'))
ax.tick_params(labelsize=8)
fig.autofmt_xdate(rotation=45)
ax.grid(True, alpha=0.3)
ax.spines['top'].set_visible(False)
ax.spines['right'].set_visible(False)
ax.legend(fontsize=8, loc='lower right')

plt.tight_layout()
plt.savefig('paper/growth.pdf', bbox_inches='tight')
print('Written paper/growth.pdf')
