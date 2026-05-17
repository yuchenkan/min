"""Generate proof growth chart for the paper."""
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.dates as mdates
from datetime import datetime

data = [
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
    ('2026-05-17', 38247),
]

dates = [datetime.strptime(d, '%Y-%m-%d') for d, _ in data]
lines = [l for _, l in data]

fig, ax = plt.subplots(figsize=(5, 3))
ax.plot(dates, [l/1000 for l in lines], 'k-o', markersize=3, linewidth=1)

# Annotations
ax.annotate('recursion theorem', xy=(datetime(2026, 5, 10), 22.3),
            xytext=(datetime(2026, 4, 30), 28),
            arrowprops=dict(arrowstyle='->', color='gray'),
            fontsize=7, color='gray')
ax.annotate('arithmetic\n(Plus, commutativity)', xy=(datetime(2026, 5, 12), 33.5),
            xytext=(datetime(2026, 5, 2), 34),
            arrowprops=dict(arrowstyle='->', color='gray'),
            fontsize=7, color='gray')
ax.annotate('TM correctness', xy=(datetime(2026, 5, 16), 39.6),
            xytext=(datetime(2026, 5, 8), 39),
            arrowprops=dict(arrowstyle='->', color='gray'),
            fontsize=7, color='gray')

ax.set_ylabel('Lines of proof code (thousands)', fontsize=9)
ax.set_ylim(15, 42)
ax.xaxis.set_major_formatter(mdates.DateFormatter('%b %d'))
ax.tick_params(labelsize=8)
fig.autofmt_xdate(rotation=45)
ax.grid(True, alpha=0.3)
ax.spines['top'].set_visible(False)
ax.spines['right'].set_visible(False)

plt.tight_layout()
plt.savefig('paper/growth.pdf', bbox_inches='tight')
print('Written paper/growth.pdf')
