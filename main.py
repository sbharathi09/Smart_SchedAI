# main.py
import os
import json
import sqlite3
import random
import io
from datetime import datetime
from flask import Flask, request, render_template_string, redirect, url_for, send_file, flash

import pdfkit

DB = "smart_sched_demo.db"
app = Flask(__name__)
app.secret_key = "dev-demo-key"

# Default config
DAYS = ["MON", "TUE", "WED", "THU", "FRI", "SAT"]
DEFAULT_ROOMS = ["B3-101","B3-102","B3-104","B3-105","B3-106","B3-107","B3-108","B3-401","B3-409"]

# init DB
def init_db():
    conn = sqlite3.connect(DB)
    c = conn.cursor()
    c.execute("""CREATE TABLE IF NOT EXISTS timetables (
                id INTEGER PRIMARY KEY,
                created_at TEXT,
                sections_json TEXT
                )""")
    c.execute("""CREATE TABLE IF NOT EXISTS exams (
                id INTEGER PRIMARY KEY,
                created_at TEXT,
                data_json TEXT
                )""")
    c.execute("""CREATE TABLE IF NOT EXISTS meetings (
                id INTEGER PRIMARY KEY,
                created_at TEXT,
                data_json TEXT
                )""")
    conn.commit()
    conn.close()
init_db()

def distribute_equal(items, total_slots):
    """Return list distributing items as equally as possible (order will be randomized)."""
    if not items:
        return []
    n = len(items)
    base = total_slots // n
    rem = total_slots % n
    allot = []
    for i, it in enumerate(items):
        count = base + (1 if i < rem else 0)
        allot += [it] * count
    random.shuffle(allot)
    return allot

def save_timetable_to_db(sections_obj):
    conn = sqlite3.connect(DB)
    c = conn.cursor()
    c.execute("INSERT INTO timetables (created_at, sections_json) VALUES (?, ?)",
              (datetime.now().isoformat(), json.dumps(sections_obj)))
    conn.commit()
    tid = c.lastrowid
    conn.close()
    return tid

def read_recent_timetables(limit=15):
    conn = sqlite3.connect(DB)
    c = conn.cursor()
    c.execute("SELECT id, created_at, sections_json FROM timetables ORDER BY id DESC LIMIT ?", (limit,))
    rows = c.fetchall()
    conn.close()
    return [{"id": r[0], "created_at": r[1], "sections": json.loads(r[2])} for r in rows]

import re

def parse_rolls(roll_input):
    """
    Convert 'ECE100-110, CAI100-110' → [['ECE100', 'ECE101'...], ['CAI100'...]]
    Supports alphanumeric prefixes.
    """
    groups = []
    for group in roll_input.split(","):
        group = group.strip()
        match = re.match(r"([A-Za-z]+)(\d+)-([A-Za-z]*)(\d+)", group)
        if match:
            prefix1, start, prefix2, end = match.groups()
            prefix = prefix1 if prefix1 else prefix2
            rolls = [f"{prefix}{i}" for i in range(int(start), int(end) + 1)]
            groups.append(rolls)
        else:
            # single roll number
            groups.append([group])
    return groups



def arrange_exam_seating(roll_input, room_list, rows, cols):
    """
    Arrange seating in a true alternating checkerboard pattern (both row & column wise)
    for two groups like 'ECE100-107, CAI100-107'.
    """
    def expand_rolls(group_str):
        # Example: "Ece100-107" -> ["Ece100", "Ece101", ...]
        prefix = ''.join([c for c in group_str if not c.isdigit()])
        digits = ''.join([c for c in group_str if c.isdigit() or c == '-'])
        if '-' in digits:
            start, end = map(int, digits.split('-'))
            return [f"{prefix}{i}" for i in range(start, end + 1)]
        else:
            return [group_str]

    # Split the input into groups (e.g., "Ece100-107, Cai100-107")
    groups = [g.strip() for g in roll_input.split(",") if g.strip()]
    if len(groups) < 2:
        return {"Error": "Please enter at least two groups for alternating seating."}

    group1 = expand_rolls(groups[0])
    group2 = expand_rolls(groups[1])

    # Prepare output dictionary
    seating = {}
    g1_index = g2_index = 0

    for room in room_list:
        room_seats = []
        for r in range(rows):
            row_data = []
            for c in range(cols):
                # True checkerboard pattern
                if (r + c) % 2 == 0:
                    if g1_index < len(group1):
                        row_data.append(group1[g1_index])
                        g1_index += 1
                    else:
                        row_data.append("")
                else:
                    if g2_index < len(group2):
                        row_data.append(group2[g2_index])
                        g2_index += 1
                    else:
                        row_data.append("")
            room_seats.append(row_data)
        seating[room] = room_seats
    return seating



# ---- Timetable generation algorithm ----
def generate_weekly_timetables_from_inputs(sections, rooms, lab_names, subjects, total_hours_per_week, break_at_idx, lunch_at_idx, periods_per_day=7):
    """
    sections: list of section names
    rooms: list of room names
    lab_names: list of lab names (strings)
    subjects: list of subject names
    total_hours_per_week: integer (hours per week per section)
    break_at_idx, lunch_at_idx: zero-based indices where break/lunch occur
    returns: dict {section: week_dict}
    """
    # We'll create a schedule per section of shape DAYS x periods_per_day.
    # Constraints:
    # - each subject must have equal number of hours per week (or as equal as possible)
    # - each lab is repeated only once a week per section and occupies 3 consecutive slots in same room
    # - no two sections may use the same room at same day+period
    # - break and lunch are set
    # Simple greedy algorithm:
    results = {}
    # track global room occupancy: {(day,period): set(rooms_used)}
    global_room_usage = {}

    # Precompute period indices that are valid for scheduling
    valid_periods = [i for i in range(periods_per_day) if i not in (break_at_idx, lunch_at_idx)]

    # Pre-generate lab placements per section (each lab only once a week)
    for sec in sections:
        # Initialize empty week
        week = {d: [None]*periods_per_day for d in DAYS}
        results[sec] = week

    # Place labs first. Each lab in lab_names should be scheduled once per section (as user requested "each lab ... repeat only once a week")
    # We'll choose random room from provided rooms or a room with lab name appended
    for sec in sections:
        week = results[sec]
        used_positions = set()
        # For each lab in lab_names, try to schedule once as 3-consecutive slots
        for lab in lab_names:
            placed = False
            # try random day/week positions
            days_shuffled = DAYS.copy()
            random.shuffle(days_shuffled)
            for day in days_shuffled:
                for start in range(0, periods_per_day - 2):
                    slots = [start, start+1, start+2]
                    # ensure not containing break/lunch
                    if any(s in (break_at_idx, lunch_at_idx) for s in slots):
                        continue
                    # ensure free in this section
                    if any(week[day][s] is not None for s in slots):
                        continue
                    # check global room availability: we must choose a room free for all three periods
                    random_rooms = rooms.copy()
                    random.shuffle(random_rooms)
                    for r in random_rooms:
                        conflict = False
                        for s in slots:
                            occ = global_room_usage.get((day,s), set())
                            if r in occ:
                                conflict = True
                                break
                        if conflict:
                            continue
                        # room free, place lab
                        for s in slots:
                            week[day][s] = f"Lab: {lab} - {r}"
                            global_room_usage.setdefault((day,s), set()).add(r)
                        placed = True
                        break
                    if placed:
                        break
                if placed:
                    break
            # Fallback: if not placed, mark as 'Lab: lab - TBA' but occupy first available slots for section only
            if not placed:
                for day in DAYS:
                    for start in range(0, periods_per_day - 2):
                        slots = [start, start+1, start+2]
                        if any(s in (break_at_idx, lunch_at_idx) for s in slots):
                            continue
                        if any(week[day][s] is not None for s in slots):
                            continue
                        for s in slots:
                            week[day][s] = f"Lab: {lab} - TBA"
                        placed = True
                        break
                    if placed:
                        break


    for sec in sections:
        week = results[sec]
        free_slots = [(d,i) for d in DAYS for i in range(periods_per_day)
                      if i not in (break_at_idx, lunch_at_idx) and (week[d][i] is None)]
 
        target_slots = min(total_hours_per_week, len(free_slots))
        # Distribute subjects equally among target_slots
        theory_list = distribute_equal(subjects, target_slots)
        # If theory_list shorter than free_slots, remaining slots fill with 'Revision/Practice'
        # Assign greedily making sure room is free (global_room_usage)
        for (pos, subj) in zip(free_slots, theory_list):
            day, idx = pos
            # choose a room free at (day,idx)
            chosen_room = None
            random_rooms = rooms.copy()
            random.shuffle(random_rooms)
            for r in random_rooms:
                occ = global_room_usage.get((day,idx), set())
                if r not in occ:
                    chosen_room = r
                    break
            if chosen_room is None:
                # no free room — mark as 'Conflict' but still assign
                week[day][idx] = f"{subj} - CONFLICT"
            else:
                week[day][idx] = f"{subj} - {chosen_room}"
                global_room_usage.setdefault((day,idx), set()).add(chosen_room)

        # fill remaining unfilled valid periods with Revision/Library
        for d in DAYS:
            for i in range(periods_per_day):
                if i == break_at_idx:
                    week[d][i] = "15-min Break"
                elif i == lunch_at_idx:
                    week[d][i] = "Lunch (45-min)"
                elif week[d][i] is None:
                    week[d][i] = "Revision/Practice"

    return results
def clear_timetable_history():
    conn = sqlite3.connect(DB)
    c = conn.cursor()
    c.execute("DELETE FROM timetables")
    conn.commit()
    conn.close()
# ----- TEMPLATES (same class names so existing styles work) -----
home_html = """
<!doctype html>
<html>
<head>
<meta charset="utf-8">
<title>SmartSched — Home</title>
<link rel="stylesheet" href="{{ url_for('static', filename='style.css') }}">
</head>
<body>
<div class="container">
  <div class="heading"><h1 align="center">SmartSched</h1></div>
  <div class="sidebar">
  <span class="nav small">
    <a href="/">Home</a> |
    <a href="/recent">Recent Timetables</a> |
    <a href="/exam_arrangement">Exam Seating Arrangement</a> |
    <a href="/study_schedule">Study Planner</a> |
    <a href="/room_availability">Room Availability</a>
  </span>
  </div>

  <div class="card">
    <h3 align="center">Generate Timetables</h3>
    <form method="post" action="/generate">
      <table class="homecard">
        <tr><td><label>Sections</label></td>
            <td><input name="sections" placeholder="AI-A,AI-B,AI-C" class="inputbox" required/></td></tr>
        <tr><td><label>Rooms</label></td>
            <td><input name="rooms" placeholder="B3-101,B3-102,..." class="inputbox" /></td></tr>
        <tr><td><label>Labs</label></td>
            <td><input name="labnames" placeholder="OS Lab,DB Lab" class="inputbox" /></td></tr>
        <tr><td><label>Subjects</label></td>
            <td><input name="subjects" placeholder="NLP,OS,CV" class="inputbox" required/></td></tr>
        <tr><td><label>Total hours / week</label></td>
            <td><input name="hours" type="number" placeholder="36 hours per a week" class="inputbox" required/></td></tr>
        <tr><td><label>Periods per day</label></td>
            <td><input name="periods" type="number" placeholder="Consider break, lunch as periods" class="inputbox" /></td></tr>
        <tr><td><label>Break at</label></td>
            <td><input name="break_at" type="number" placeholder="Enter Break at " class="inputbox" /></td></tr>
        <tr><td><label>Lunch at</label></td>
            <td><input name="lunch_at" type="number" placeholder="Enter Lunch at" class="inputbox" /></td></tr>
        <tr><td colspan="2" align="center"><button type="submit" class="mbutton">Generate Timetable</button></td></tr>
      </table>
    </form>
    <!--p class="small">Notes: provide comma-separated lists for multi-values. Lab sessions are scheduled as 3 consecutive periods once per lab per section. The system tries to avoid room conflicts.</p>
  </div>

  <div class="card">
    <h3>Quick Links</h3>
    <a href="/recent">Recent Timetables</a> |
    <a href="/exam_arrangement">Exam Seating Arrangement</a-->
  </div>
</div>
</body>
</html>
"""
result_html = """
<!doctype html>
<html>
<head>
<meta charset="utf-8">
<title>Timetable Result</title>
<link rel="stylesheet" href="{{ url_for('static', filename='style.css') }}">
</head>
<body>
<div class="container">
  <button class="home"><a href="/">HOME</a></button>
  
  <h1 align="center">Generated Timetables</h1>
  <p class="small">Created at: {{ created }}</p>

  {% for sec, week in sections.items() %}
    <div class="cards" data-sec="{{ sec }}">
      <h3>{{ sec }}</h3>
      <table style="border: 3px solid #115072;">
        <thead>
          <tr><th>Day / Period</th>
          {% for p in range(periods) %}
            <th>P{{p+1}}</th>
          {% endfor %}
          </tr>
        </thead>
        <tbody>
          {% for day, slots in week.items() %}
            <tr><td><strong>{{ day }}</strong></td>
            {% for s in slots %}<td>{{ s }}</td>{% endfor %}
            </tr>
          {% endfor %}
        </tbody>
      </table>
      <div style="margin-top:8px;">
        <!-- ✅ changed from POST form to browser print button -->
        <button type="button" class="home" onclick="printSection('{{ sec }}')">Print / Save {{ sec }} as PDF</button>
      </div>
    </div>
  {% endfor %}

  <div style="margin:12px 0;">
    <a class="button" href="/recent">View Recent Timetables</a><br>
    <button onclick="window.print()" class="mbutton">Print / Save All as PDF</button>
  </div>
</div>

<!-- ✅ added printSection() JavaScript -->

<script>
function printSection(sectionId) {
  const content = document.querySelector(`[data-sec="${sectionId}"]`).outerHTML;
  const printWindow = window.open('', '', 'width=900,height=700');
  printWindow.document.write(`
    <html>
      <head>
        <title>Timetable - ${sectionId}</title>
        <style>
          body { font-family: Arial; padding: 20px; }
          table { width: 100%; border-collapse: collapse; }
          th, td { border: 1px solid #000; padding: 6px; text-align: center; }
          h3 { text-align: center; }
          @media print { button { display: none; } }
        </style>
      </head>
      <body>
        ${content}
        <script>
          window.onload = function(){
            window.print();
            window.onafterprint = function(){ window.close(); };
          };
        <\/script>
      </body>
    </html>
  `);
  printWindow.document.close();
}
</script>


</body>
</html>
"""



recent_html = """
<!doctype html>
<html>
<head>
<meta charset="utf-8">
<title>Recent Timetables</title>
<link rel="stylesheet" href="{{ url_for('static', filename='style.css') }}">
</head>
<body>
<div class="container">
  <button class="home"><a href="/">HOME</a></button>
  <div style="display:flex; justify-content:space-between; align-items:center; margin-bottom:15px;">

<h1 style="margin:0;">Recent Timetables (last {{ items|length }})</h1>

<a href="/clear_history">
<button class="mbutton" style="background:#c62828;">Clear History</button>
</a>

</div>
  {% if items %}
    {% for it in items %}
      <div class="cards">
        <div class="small">ID: {{ it.id }} — Created: {{ it.created_at }}</div>
        {% for sec, week in it.sections.items() %}
          <h4>{{ sec }}</h4>
          <table style="border: 3px solid #115072;">
            <thead><tr><th>Day</th>{% for p in range(periods) %}<th>P{{ p+1 }}</th>{% endfor %}</tr></thead>
            <tbody>
              {% for day, slots in week.items() %}
                <tr><td>{{ day }}</td>{% for s in slots %}<td>{{ s }}</td>{% endfor %}</tr>
              {% endfor %}
            </tbody>
          </table>
        {% endfor %}
      </div>
    {% endfor %}
  {% else %}
    <div class="alert">No timetables saved yet.</div>
  {% endif %}
</div>
</body>
</html>
"""

exam_html = """
<!doctype html>
<html>
<head>
<meta charset="utf-8">
<title>Exam Seating</title>
<link rel="stylesheet" href="{{ url_for('static', filename='style.css') }}">
</head>
<body>
<div class="container">
  <button class="home"><a href="/">HOME</a></button>
  <h1 align="center">Exam Seating Arrangement</h1>
  <form method="post" action="/exam_arrangement" target="_blank">
    <div class="card">
      <table>
        <tr><td><label>Rolls (range or comma list)</label></td>
            <td><input name="rolls" placeholder="ECE100-200 or CAI200-300" class="inputbox" required/></td></tr>
        <tr><td><label>Rooms (comma)</label></td>
            <td><input name="rooms" placeholder="B3-101,B3-102" class="inputbox" required/></td></tr>
        <tr><td><label>No Of Rows</td>
            <td><input name="rows" placeholder="5" class="inputbox" required/></td></tr>
        <tr><td><label>No Of Columns</td>
            <td><input name="cols" placeholder="5" class="inputbox" required/></td></tr>
      </table>
    </div>
    <button type="submit" class="mbutton">Generate Seating</button>
  </form>
</div>
</body>
</html>
"""
exam_result_html = """
<!doctype html>
<html>
<head>
<meta charset="utf-8">
<title>Exam Seating Result</title>
<link rel="stylesheet" href="{{ url_for('static', filename='style.css') }}">
</head>
<body>
<div class="container">
<h1 align="center">Exam Seating Arrangement</h1>

{% for room, grid in seating.items() %}
  <div class="cards">
    <h3>{{ room }}</h3>
    <table style="border:3px solid #115072; text-align:center;">
      {% for row in grid %}
        <tr>
          {% for seat in row %}
            <td style="padding:8px;">{{ seat }}</td>
          {% endfor %}
        </tr>
      {% endfor %}
    </table>
  </div>
{% endfor %}

<button onclick="window.print()" class="mbutton">Print / Save as PDF</button>
</div>
</body>
</html>
"""

study_html = """
<!doctype html>
<html>
<head>
<meta charset="utf-8">
<title>Study Planner</title>
<link rel="stylesheet" href="{{ url_for('static', filename='style.css') }}">
</head>
<body>
<div class="container">
  <button class="home"><a href="/">HOME</a></button>
  <h1 align="center">Student Study Planner</h1>
  <form method="post" action="/study_schedule" target="_blank">
    <div class="card">
    <table>
      <tr><td><label>Core Subjects (comma)</label></td><td><input name="core_subjects" class="inputbox" placeholder="Math,Physics"/></td></tr>
      <tr><td><label>Skill Subjects (comma)</label></td><td><input name="skill_subjects" class="inputbox" placeholder="coding, prepinsta corse"/></td></tr>
      <tr><td><label>Morning hours (comma per subject)</label></td><td><input name="mrng" class="inputbox" placeholder="1,2"/></td></tr>
      <tr><td><label>Evening hours (comma per subject)</label></td><td><input name="evng" class="inputbox" placeholder="1,1"/></td></tr>
    </table>
    </div>
    <button type="submit" class="mbutton">Generate Plan</button>
  </form>
</div>
</body>
</html>
"""
study_result_html = """
<!doctype html>
<html>
<head>
<meta charset="utf-8">
<title>Study Plan</title>
<link rel="stylesheet" href="{{ url_for('static', filename='style.css') }}">
</head>
<body>
<div class="container">
<h1 align="center">Weekly Study Planner</h1>

<table style="border:3px solid #115072;">
<tr><th>Day</th><th>Morning</th><th>Evening</th></tr>
{% for day, info in plan.items() %}
<tr>
<td>{{ day }}</td>
<td>{{ info.morning }}</td>
<td>{{ info.evening }}</td>
</tr>
{% endfor %}
</table>

<button onclick="window.print()" class="mbutton">Print / Save as PDF</button>
</div>
</body>
</html>
"""

room_html = """
<!doctype html>
<html>
<head>
<meta charset="utf-8">
<title>Room Availability</title>
<link rel="stylesheet" href="{{ url_for('static', filename='style.css') }}">
</head>
<body>
<div class="container">
  <button class="home"><a href="/">HOME</a></button>
  <h1 align="center">Room Availability Check</h1>
  <form method="post" action="/room_availability">
    <div class="card">
      <table>
        <tr><td><label>Day</label></td>
            <td><select name="day">{% for d in days %}<option>{{ d }}</option>{% endfor %}</select></td></tr>
        <tr><td><label>Period index (1..{{ periods }})</label></td>
            <td><input name="period" type="number" class="inputbox" value="1" /></td></tr>
        <tr><td><label>Rooms (comma)</label></td>
            <td><input name="rooms" class="inputbox" placeholder="(optional)"/></td></tr>
      </table>
    </div>
    <button type="submit" class="mbutton">Check Availability</button>
  </form>

  {% if available is defined %}
    <div class="card">
      <h3>Used Rooms</h3>
      <div class="small">{{ available.used | join(', ') if available.used else 'None' }}</div>
      <h3>Available Rooms</h3>
      <div class="small">{{ available.available | join(', ') if available.available else 'No rooms free' }}</div>
    </div>
  {% endif %}
</div>
</body>
</html>
"""

# ---------------- Routes ----------------

@app.route("/")
def home():
    return render_template_string(home_html)

@app.route("/generate", methods=["POST"])
def generate():
    sections_raw = request.form.get("sections", "CSE-A,CSE-B")
    rooms_raw = request.form.get("rooms", ",".join(DEFAULT_ROOMS))
    labnames_raw = request.form.get("labnames", "")
    subjects_raw = request.form.get("subjects", "")
    hours = int(request.form.get("hours", "30") or 30)
    periods = int(request.form.get("periods", "7") or 7)
    break_at = int(request.form.get("break_at", "3") or 3) - 1
    lunch_at = int(request.form.get("lunch_at", "5") or 5) - 1

    sections = [s.strip() for s in sections_raw.split(",") if s.strip()]
    rooms = [r.strip() for r in rooms_raw.split(",") if r.strip()]
    lab_names = [s.strip() for s in labnames_raw.split(",") if s.strip()]
    subjects = [s.strip() for s in subjects_raw.split(",") if s.strip()]

    # If no rooms provided, use defaults
    if not rooms:
        rooms = DEFAULT_ROOMS.copy()
    # If no lab names, we create generic labs
    if not lab_names:
        lab_names = ["Lab1"]

    timetables = generate_weekly_timetables_from_inputs(sections, rooms, lab_names, subjects, hours, break_at, lunch_at, periods_per_day=periods)
    tid = save_timetable_to_db(timetables)
    created = datetime.now().isoformat()
    return render_template_string(result_html, sections=timetables, created=created, periods=periods, timetable_id=tid)

# Example route to show timetable results
@app.route("/view_timetable/<int:tid>")
def view_timetable(tid):
    conn = sqlite3.connect(DB)
    c = conn.cursor()
    c.execute("SELECT sections_json, created_at FROM timetables WHERE id=?", (tid,))
    row = c.fetchone()
    conn.close()

    if not row:
        return "Timetable not found", 404

    sections = json.loads(row[0])
    created = row[1]
    periods = len(next(iter(sections.values())).get(next(iter(sections.values())), []))

    return render_template_string(result_html, created=created, sections=sections, periods=periods)

@app.route("/recent")
def recent():
    items = read_recent_timetables(limit=15)
    periods = 7
    if items:
        first = items[0]
        if first["sections"]:
            sec = next(iter(first["sections"].values()))
            periods = len(next(iter(sec.values())))
    return render_template_string(recent_html, items=items, periods=periods)

import re
@app.route("/exam_arrangement", methods=["GET","POST"])
def exam_arrangement():
    if request.method == "POST":
        roll_input = request.form["rolls"]
        room_input = request.form["rooms"]
        rows = int(request.form["rows"])
        cols = int(request.form["cols"])

        rooms = [r.strip() for r in room_input.split(",")]
        seating = arrange_exam_seating(roll_input, rooms, rows, cols)

        return render_template_string(exam_result_html, seating=seating)

    return render_template_string(exam_html)

@app.route("/study_schedule", methods=["GET","POST"])
def study_schedule():
    if request.method == "POST":
        core = request.form.get("core_subjects","").split(",")
        skill = request.form.get("skill_subjects","").split(",")

        DAYS = ["Monday","Tuesday","Wednesday","Thursday","Friday","Saturday"]
        plan = {}

        for i, day in enumerate(DAYS):
            plan[day] = {
                "morning": core[i % len(core)].strip() if core[0] else "Free",
                "evening": skill[i % len(skill)].strip() if skill[0] else "Free"
            }

        return render_template_string(study_result_html, plan=plan)

    return render_template_string(study_html)


@app.route("/room_availability", methods=["GET","POST"])
def room_availability():
    available = None
    if request.method == "POST":
        day = request.form.get("day")
        period = int(request.form.get("period", "1")) - 1
        rooms_raw = request.form.get("rooms", "")
        rooms = [r.strip() for r in rooms_raw.split(",") if r.strip()] if rooms_raw else DEFAULT_ROOMS.copy()
        # Check recent timetables
        used = set()
        items = read_recent_timetables(limit=100)
        for item in items:
            secs = item["sections"]
            for sec_name, week in secs.items():
                if day in week:
                    slot = week[day][period]
                    if "-" in slot:
                        parts = slot.split("-")
                        room = parts[-1].strip()
                        used.add(room)
        available_rooms = [r for r in rooms if r not in used]
        available = {"used": sorted(list(used)), "available": available_rooms}
    return render_template_string(room_html, days=DAYS, periods=7, available=available)
@app.route("/clear_history")
def clear_history():
    clear_timetable_history()
    return redirect(url_for("recent"))
if __name__ == "__main__":
    app.run(debug=True)

"""
python -m venv venv 
venv\Scripts\activate
python main.py
"""