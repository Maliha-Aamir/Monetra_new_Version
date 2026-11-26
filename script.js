/* =========================================================
   MONETRA - script.js
   Navigation, storage, forms, calculations, dashboard,
   recurring entries, safe deletion with confirmation and Undo,
   record relationships, duplicate income warnings, CSV export,
   backup and restore, first-time setup, reset all data
   ========================================================= */

(function () {
  "use strict";

  /* ---------------------------------------------------------
     1. CONSTANTS
     --------------------------------------------------------- */
  var STORAGE_KEY = "calmBudget.v1";
  var CORRUPT_BACKUP_KEY = "calmBudget.v1.corruptBackup";
  // Keys used by older versions of the app (demo mode). Removed on start.
  var LEGACY_KEYS = ["calmBudget.demo", "calmBudget.mode"];
  var DATA_VERSION = 1;
  // Marks data that has been through the relationship check (bill <-> payment links etc.)
  var RELATIONS_VERSION = 2;

  var PAGES = ["home", "money", "budgets", "bills", "goals", "debts", "more"];
  var DEBT_CATEGORY = "__debt__";   // marks expenses that are debt payments (not a user category)
  var DEFAULT_PAGE = "home";

  var CURRENCIES = ["USD", "EUR", "GBP", "PKR", "INR", "AED", "SAR", "CAD", "AUD"];
  var PAYMENT_METHODS = ["Cash", "Card", "Bank transfer", "Mobile wallet", "Other"];
  var FREQUENCIES = [
    { value: "weekly", label: "Weekly" },
    { value: "monthly", label: "Monthly" },
    { value: "yearly", label: "Yearly" }
  ];
  var DEFAULT_CATEGORIES = [
    "Food & Groceries", "Transport", "Bills & Utilities", "Housing",
    "Health", "Shopping", "Education", "Entertainment", "Other"
  ];
  var MONTH_NAMES = ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"];

  var MAX_CENTS = 99999999999;
  var MAX_LIST_ROWS = 8;
  var MAX_HISTORY_ROWS = 200;
  var UNDO_MS = 8000;

  /* ---------------------------------------------------------
     2. APP STATE
     --------------------------------------------------------- */
  var data = null;
  var storageWorks = true;
  var toastTimer = null;
  var undoAction = null;
  var currentForm = null;
  var formatters = {};
  var lastRenderDay = "";
  var catchUpActive = false;   // true once, when someone returns after a few days away
  var reviewOffset = 0;   // 0 = this budget period, -1 = the one before, ...
  var formSubmitting = false;   // blocks a second submit while one is being processed

  /* ---------------------------------------------------------
     3. SMALL HELPERS
     --------------------------------------------------------- */
  function $(id) {
    return document.getElementById(id);
  }

  function isPlainObject(value) {
    return value !== null && typeof value === "object" && !Array.isArray(value);
  }

  function isInt(value) {
    return typeof value === "number" && isFinite(value) && Math.floor(value) === value;
  }

  function fillMissing(target, defaults) {
    Object.keys(defaults).forEach(function (key) {
      if (target[key] === undefined) {
        target[key] = defaults[key];
      } else if (isPlainObject(defaults[key]) && isPlainObject(target[key])) {
        fillMissing(target[key], defaults[key]);
      }
    });
    return target;
  }

  function uid() {
    return "x" + Date.now().toString(36) + Math.random().toString(36).slice(2, 8);
  }

  function esc(value) {
    var map = { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" };
    return String(value == null ? "" : value).replace(/[&<>"']/g, function (ch) {
      return map[ch];
    });
  }

  function plural(n, word) {
    return n + " " + word + (n === 1 ? "" : "s");
  }

  function findById(list, id) {
    for (var i = 0; i < list.length; i++) {
      if (list[i].id === id) {
        return list[i];
      }
    }
    return null;
  }

  function removeById(list, id) {
    for (var i = 0; i < list.length; i++) {
      if (list[i].id === id) {
        return { item: list.splice(i, 1)[0], index: i };
      }
    }
    return null;
  }

  // Puts a removed record back at its old place. Never adds a second copy of the same id.
  function restoreAt(list, record) {
    if (!record || !record.item || findById(list, record.item.id)) {
      return false;
    }
    list.splice(Math.min(record.index, list.length), 0, record.item);
    return true;
  }

  function quoted(name) {
    return "\u201C" + name + "\u201D";
  }

  function showBanner(id, message) {
    var app = $("app");
    if (!app || $(id)) {
      return;
    }
    var banner = document.createElement("div");
    banner.className = "app-banner";
    banner.id = id;
    banner.setAttribute("role", "status");
    banner.textContent = message;
    app.insertBefore(banner, app.firstChild);
  }

  function frequencyLabel(value) {
    for (var i = 0; i < FREQUENCIES.length; i++) {
      if (FREQUENCIES[i].value === value) { return FREQUENCIES[i].label; }
    }
    return "Monthly";
  }

  /* ---------------------------------------------------------
     4. DATES (all dates are "YYYY-MM-DD" text)
     --------------------------------------------------------- */
  function pad2(n) {
    return (n < 10 ? "0" : "") + n;
  }

  function todayStr() {
    var d = new Date();
    return d.getFullYear() + "-" + pad2(d.getMonth() + 1) + "-" + pad2(d.getDate());
  }

  function isValidDate(s) {
    if (typeof s !== "string" || !/^\d{4}-\d{2}-\d{2}$/.test(s)) {
      return false;
    }
    var d = new Date(Date.UTC(+s.slice(0, 4), +s.slice(5, 7) - 1, +s.slice(8, 10)));
    return d.toISOString().slice(0, 10) === s;
  }

  function addDays(s, n) {
    var d = new Date(Date.UTC(+s.slice(0, 4), +s.slice(5, 7) - 1, +s.slice(8, 10) + n));
    return d.toISOString().slice(0, 10);
  }

  function daysBetween(a, b) {
    var da = Date.UTC(+a.slice(0, 4), +a.slice(5, 7) - 1, +a.slice(8, 10));
    var db = Date.UTC(+b.slice(0, 4), +b.slice(5, 7) - 1, +b.slice(8, 10));
    return Math.round((db - da) / 86400000);
  }

  function daysInMonth(year, month) {
    return new Date(Date.UTC(year, month, 0)).getUTCDate();
  }

  // Add n months to a date, keeping the "anchor" day where the month is long enough
  function addMonths(s, n, anchorDay) {
    var total = (+s.slice(0, 4)) * 12 + (+s.slice(5, 7) - 1) + n;
    var y = Math.floor(total / 12);
    var m = (total % 12) + 1;
    var d = Math.min(anchorDay, daysInMonth(y, m));
    return y + "-" + pad2(m) + "-" + pad2(d);
  }

  function nextOccurrence(date, frequency, anchorDay) {
    if (frequency === "weekly") {
      return addDays(date, 7);
    }
    return addMonths(date, frequency === "yearly" ? 12 : 1, anchorDay);
  }

  function formatDate(s) {
    return parseInt(s.slice(8, 10), 10) + " " + MONTH_NAMES[parseInt(s.slice(5, 7), 10) - 1] + " " + s.slice(0, 4);
  }

  function formatShortDate(s) {
    return parseInt(s.slice(8, 10), 10) + " " + MONTH_NAMES[parseInt(s.slice(5, 7), 10) - 1];
  }

  // Budget period: from the month start day to the day before the next start day
  function getPeriod(today, startDay) {
    var y = +today.slice(0, 4);
    var m = +today.slice(5, 7);
    var d = +today.slice(8, 10);
    var sy = y;
    var sm = m;
    if (d < startDay) {
      sm -= 1;
      if (sm < 1) {
        sm = 12;
        sy -= 1;
      }
    }
    var ey = sy;
    var em = sm + 1;
    if (em > 12) {
      em = 1;
      ey += 1;
    }
    var start = sy + "-" + pad2(sm) + "-" + pad2(startDay);
    var nextStart = ey + "-" + pad2(em) + "-" + pad2(startDay);
    return { start: start, end: addDays(nextStart, -1) };
  }

  function formatPeriod(p) {
    return formatShortDate(p.start) + " - " + formatDate(p.end);
  }

  function checkDate(value, noFuture) {
    if (!isValidDate(value)) {
      return "Please choose a valid date.";
    }
    if (value < "2000-01-01" || value > "2100-12-31") {
      return "Please choose a date between the years 2000 and 2100.";
    }
    if (noFuture && value > todayStr()) {
      return "Please choose today or an earlier date.";
    }
    return "";
  }

  /* ---------------------------------------------------------
     5. MONEY (stored as integer cents: 10.50 = 1050)
     --------------------------------------------------------- */
  function parseMoney(text) {
    var cleaned = String(text).replace(/[\s,]/g, "");
    if (!/^\d+(\.\d{1,2})?$/.test(cleaned)) {
      return null;
    }
    var parts = cleaned.split(".");
    var whole = parseInt(parts[0], 10);
    var fraction = parts[1] ? parseInt((parts[1] + "0").slice(0, 2), 10) : 0;
    var cents = whole * 100 + fraction;
    if (!isFinite(cents) || cents > MAX_CENTS) {
      return null;
    }
    return cents;
  }

  function centsToInput(cents) {
    var whole = Math.floor(cents / 100);
    var fraction = cents % 100;
    return whole + "." + pad2(fraction);
  }

  function getFormatter(code, digits) {
    var key = code + "|" + digits;
    if (!formatters[key]) {
      try {
        formatters[key] = new Intl.NumberFormat("en-US", {
          style: "currency",
          currency: code,
          minimumFractionDigits: digits,
          maximumFractionDigits: digits
        });
      } catch (error) {
        formatters[key] = new Intl.NumberFormat("en-US", {
          minimumFractionDigits: digits,
          maximumFractionDigits: digits
        });
      }
    }
    return formatters[key];
  }

  function formatMoney(cents) {
    var wholeAmount = cents % 100 === 0;
    return getFormatter(data.settings.currency, wholeAmount ? 0 : 2).format(cents / 100);
  }

  /* ---------------------------------------------------------
     6. STORAGE
     --------------------------------------------------------- */
  function createDefaultData() {
    return {
      version: DATA_VERSION,
      createdAt: new Date().toISOString(),
      categoriesSeeded: false,
      setupCompleted: false,
      settings: { name: "", currency: "USD", monthStartDay: 1, focusMode: false, largeText: false, reducedMotion: null },
      categories: [],
      transactions: [],
      bills: [],
      recurring: [],
      goals: [],
      budgets: [],
      debts: []
    };
  }

  // Notes about repairs made during the last load. Shown once when the app opens.
  var migrationNotes = [];

  /* Makes sure every record has a stable id and that bills and their payment
     expenses point at each other. Nothing is ever deleted here: a record that
     cannot be linked safely is kept as a normal record. Safe to run many times. */
  function migrateRelationships(d) {
    var notes = [];

    function ensureIds(list) {
      var seen = {};
      list.forEach(function (item) {
        if (!isPlainObject(item)) { return; }
        if (typeof item.id !== "string" || item.id === "" || seen[item.id]) {
          item.id = uid();
        }
        seen[item.id] = true;
      });
    }

    ["categories", "transactions", "bills", "goals", "budgets", "recurring", "debts"].forEach(function (key) {
      ensureIds(d[key]);
    });

    // Goal contributions belong to exactly one goal: make that explicit
    d.goals.forEach(function (g) {
      if (!isPlainObject(g)) { return; }
      ensureIds(g.contributions);
      g.contributions.forEach(function (c) {
        if (isPlainObject(c)) { c.goalId = g.id; }
      });
    });

    // Debts: every payment has an id, and a debt payment expense must point at a real debt and payment
    var debtPay = {};
    d.debts.forEach(function (x) {
      if (!isPlainObject(x)) { return; }
      if (!Array.isArray(x.payments)) { x.payments = []; }
      if (!isInt(x.paidBefore) || x.paidBefore < 0) { x.paidBefore = 0; }
      if (x.interestRate !== undefined && x.interestRate !== null && !isValidRate(x.interestRate)) { x.interestRate = null; }
      ensureIds(x.payments);
      x.payments.forEach(function (p) { if (isPlainObject(p)) { debtPay[p.id] = x.id; } });
    });
    d.transactions.forEach(function (t) {
      if (isPlainObject(t) && t.debtId && debtPay[t.debtPaymentId] !== t.debtId) { t.debtId = ""; t.debtPaymentId = ""; }
    });

    // Bills <-> payment expenses
    var billIds = {};
    d.bills.forEach(function (b) {
      if (isPlainObject(b)) { billIds[b.id] = true; }
    });

    var byBill = {};
    var orphaned = 0;
    d.transactions.forEach(function (t) {
      if (!isPlainObject(t) || !t.billId) { return; }
      if (!billIds[t.billId] || t.type !== "expense") {
        // The bill is gone (or the link makes no sense): keep it as a normal record
        t.billId = "";
        orphaned++;
        return;
      }
      (byBill[t.billId] = byBill[t.billId] || []).push(t);
    });

    var extras = 0;
    var fixedPaid = 0;
    d.bills.forEach(function (b) {
      if (!isPlainObject(b)) { return; }
      var list = (byBill[b.id] || []).slice().sort(function (x, y) {
        return (x.createdAt || 0) - (y.createdAt || 0);
      });
      var chosen = null;
      if (b.linkedExpenseId) {
        list.forEach(function (t) { if (t.id === b.linkedExpenseId) { chosen = t; } });
      }
      if (!chosen && list.length) { chosen = list[0]; }
      list.forEach(function (t) {
        if (t !== chosen) {
          t.billId = "";   // a second "payment" for one bill: keep it, but as a normal expense
          extras++;
        }
      });
      // Never take over an expense that does not carry this bill's id
      b.linkedExpenseId = chosen ? chosen.id : null;
      if (chosen && !b.paid) {
        b.paid = true;     // the payment exists, so the bill is paid (stops double counting)
        fixedPaid++;
      }
      if (typeof b.paid !== "boolean") { b.paid = !!b.paid; }
    });

    if (orphaned) { notes.push(plural(orphaned, "payment record") + " had no matching bill and now " + (orphaned === 1 ? "is a normal expense." : "are normal expenses.")); }
    if (extras) { notes.push(plural(extras, "extra payment") + " for one bill " + (extras === 1 ? "was" : "were") + " kept as normal " + (extras === 1 ? "expense." : "expenses.")); }
    if (fixedPaid) { notes.push(plural(fixedPaid, "bill") + " with a payment " + (fixedPaid === 1 ? "was" : "were") + " marked as paid."); }

    migrationNotes = notes;
    d.relationsVersion = RELATIONS_VERSION;
  }

  function normalizeData(d) {
    fillMissing(d, createDefaultData());
    ["categories", "transactions", "bills", "recurring", "goals", "budgets", "debts"].forEach(function (key) {
      if (!Array.isArray(d[key])) {
        d[key] = [];
      }
    });
    if (!isPlainObject(d.settings)) {
      d.settings = createDefaultData().settings;
    }
    var s = d.settings;
    if (typeof s.name !== "string") {
      s.name = "";
    }
    if (CURRENCIES.indexOf(s.currency) === -1) {
      s.currency = "USD";
    }
    s.monthStartDay = parseInt(s.monthStartDay, 10);
    if (!(s.monthStartDay >= 1 && s.monthStartDay <= 28)) {
      s.monthStartDay = 1;
    }
    s.focusMode = s.focusMode === true;
    s.largeText = s.largeText === true;
    if (typeof s.reducedMotion !== "boolean") { s.reducedMotion = null; }
    d.goals.forEach(function (g) {
      if (!Array.isArray(g.contributions)) {
        g.contributions = [];
      }
      if (!isInt(g.monthlyPlan) || g.monthlyPlan < 0) {
        g.monthlyPlan = 0;
      }
    });
    d.recurring = d.recurring.filter(function (r) {
      return isPlainObject(r) && typeof r.id === "string" && (r.type === "income" || r.type === "expense") &&
        isInt(r.amount) && r.amount > 0 && isValidDate(r.nextDate);
    });
    d.recurring.forEach(function (r) {
      if (["weekly", "monthly", "yearly"].indexOf(r.frequency) === -1) {
        r.frequency = "monthly";
      }
      if (typeof r.active !== "boolean") {
        r.active = true;
      }
      if (!isInt(r.anchorDay) || r.anchorDay < 1 || r.anchorDay > 31) {
        r.anchorDay = +r.nextDate.slice(8, 10);
      }
    });
    if (!d.categoriesSeeded) {
      if (d.categories.length === 0) {
        d.categories = DEFAULT_CATEGORIES.map(function (name) {
          return { id: uid(), name: name };
        });
      }
      d.categoriesSeeded = true;
    }
    migrateRelationships(d);
    return d;
  }

  function checkStorageWorks() {
    try {
      var testKey = "__calmBudgetTest__";
      window.localStorage.setItem(testKey, "1");
      window.localStorage.removeItem(testKey);
      return true;
    } catch (error) {
      return false;
    }
  }

  function saveData() {
    if (!storageWorks) {
      return false;
    }
    try {
      window.localStorage.setItem(STORAGE_KEY, JSON.stringify(data));
      return true;
    } catch (error) {
      showBanner(
        "save-error-banner",
        "Your latest changes could not be saved. Your browser storage may be full or blocked."
      );
      return false;
    }
  }

  /* True only for saved data that holds nothing of the user's: no records, no name,
     default settings and default (or no) categories. Such data comes from an older
     version of the app that was opened once and never used. It is safe to show the
     Welcome screen for it, and nothing is deleted. Any real data returns false. */
  function isUntouchedData(p) {
    var lists = ["transactions", "bills", "goals", "budgets", "recurring", "debts"];
    for (var i = 0; i < lists.length; i++) {
      var list = p[lists[i]];
      if (list !== undefined && (!Array.isArray(list) || list.length > 0)) { return false; }
    }
    if (p.settings !== undefined) {
      if (!isPlainObject(p.settings)) { return false; }
      var s = p.settings;
      if (s.name !== undefined && String(s.name).trim() !== "") { return false; }
      if (s.currency !== undefined && s.currency !== "USD") { return false; }
      if (s.monthStartDay !== undefined && parseInt(s.monthStartDay, 10) !== 1) { return false; }
    }
    if (p.categories !== undefined) {
      if (!Array.isArray(p.categories)) { return false; }
      if (p.categories.length > 0) {
        if (p.categories.length !== DEFAULT_CATEGORIES.length) { return false; }
        for (var j = 0; j < p.categories.length; j++) {
          if (!isPlainObject(p.categories[j]) || DEFAULT_CATEGORIES.indexOf(p.categories[j].name) === -1) { return false; }
        }
      }
    }
    return true;
  }

  function loadFromKey(key) {
    var raw = null;
    try {
      raw = window.localStorage.getItem(key);
    } catch (error) {
      storageWorks = false;
      return { status: "error" };
    }
    if (raw === null) {
      return { status: "empty" };
    }
    try {
      var parsed = JSON.parse(raw);
      if (!isPlainObject(parsed) || typeof parsed.version !== "number" || parsed.version > DATA_VERSION) {
        throw new Error("Unexpected data format");
      }
      // Data saved before first-time setup existed: a real existing user skips setup,
      // but an untouched empty app (nothing entered, nothing changed) still gets the Welcome screen.
      if (typeof parsed.setupCompleted !== "boolean") {
        parsed.setupCompleted = !isUntouchedData(parsed);
      }
      // Anyone who already has saved records is a returning user: never show setup to them
      if (parsed.setupCompleted !== true && ["transactions", "bills", "goals", "budgets", "recurring", "debts"].some(function (k) {
        return Array.isArray(parsed[k]) && parsed[k].length > 0;
      })) {
        parsed.setupCompleted = true;
      }
      return { status: "ok", value: normalizeData(parsed) };
    } catch (error) {
      return { status: "corrupt", raw: raw };
    }
  }

  function loadPersonalData() {
    var result = loadFromKey(STORAGE_KEY);
    if (result.status === "ok") {
      return result.value;
    }
    if (result.status === "corrupt") {
      try {
        window.localStorage.setItem(CORRUPT_BACKUP_KEY, result.raw);
      } catch (error) {
        /* ignore */
      }
      showBanner(
        "corrupt-data-banner",
        "Your saved data could not be read, so the app started fresh. A copy of the old data was kept in this browser."
      );
    }
    return normalizeData(createDefaultData());
  }

  function removeLegacyKeys() {
    LEGACY_KEYS.forEach(function (key) {
      try {
        window.localStorage.removeItem(key);
      } catch (error) {
        /* ignore */
      }
    });
  }

  /* ---------------------------------------------------------
     7. CATEGORY HELPERS
     --------------------------------------------------------- */
  function getCategory(id) {
    return findById(data.categories, id);
  }

  function categoryName(id) {
    var c = getCategory(id);
    return c ? c.name : (id === DEBT_CATEGORY ? "Debt payments" : "Uncategorized");
  }

  function sortedCategories() {
    return data.categories.slice().sort(function (a, b) {
      return a.name.toLowerCase() < b.name.toLowerCase() ? -1 : 1;
    });
  }

  function categoryOptions() {
    return sortedCategories().map(function (c) {
      return { value: c.id, label: c.name };
    });
  }

  /* ---------------------------------------------------------
     8. RECURRING ENTRIES (creates real transactions, never twice)
     --------------------------------------------------------- */
  function buildRecurringTx(r, date) {
    var t = {
      id: uid(), type: r.type, amount: r.amount, date: date,
      method: r.method || "", recurringId: r.id, createdAt: Date.now()
    };
    if (r.type === "income") {
      t.source = r.source;
    } else {
      t.categoryId = r.categoryId;
    }
    return t;
  }

  // Adds every entry that is due (nextDate is today or earlier). Returns true if anything changed.
  function processRecurring() {
    var today = todayStr();
    var changed = false;
    data.recurring.forEach(function (r) {
      if (!r.active) { return; }
      var guard = 0;
      while (r.nextDate <= today && guard < 400) {
        guard++;
        var date = r.nextDate;
        var exists = data.transactions.some(function (t) {
          return t.recurringId === r.id && t.date === date;
        });
        if (!exists) {
          data.transactions.push(buildRecurringTx(r, date));
        }
        r.nextDate = nextOccurrence(date, r.frequency, r.anchorDay);
        changed = true;
      }
    });
    return changed;
  }

  /* ---------------------------------------------------------
     8b. DUPLICATE INCOME DETECTION
     Warns (never blocks) when a manual income and a recurring income
     may be the same money. It only reads data: nothing is deleted,
     merged, skipped or changed. A match needs the SAME amount, a
     SIMILAR source and a date in the SAME period. Amount alone is
     never enough, and two manual incomes are never compared.
     --------------------------------------------------------- */
  // Returned by a form's onSubmit to say "the form stays open, a question is showing"
  var FORM_PENDING = { pending: true };
  // How close two dates must be to count as the same occurrence
  var DUP_NEAR_DAYS = { weekly: 3, yearly: 14 };
  var DUP_DEFAULT_DAYS = 3;

  function sourceTokens(text) {
    return String(text == null ? "" : text).toLowerCase()
      .replace(/[^a-z0-9\u00c0-\uffff]+/g, " ").trim().split(" ")
      .filter(function (w) { return w.length > 0; });
  }

  // "Salary", "salary " and "Salary - Acme" count as the same source
  function sameSource(a, b) {
    var ta = sourceTokens(a);
    var tb = sourceTokens(b);
    if (!ta.length || !tb.length) { return false; }
    var small = ta.length <= tb.length ? ta : tb;
    var big = small === ta ? tb : ta;
    return small.every(function (word) { return big.indexOf(word) !== -1; });
  }

  // Monthly: same budget period. Weekly / yearly (or unknown): dates close together.
  function sameIncomeWindow(frequency, dateA, dateB) {
    if (frequency === "monthly") {
      var startDay = data.settings.monthStartDay;
      return getPeriod(dateA, startDay).start === getPeriod(dateB, startDay).start;
    }
    var days = DUP_NEAR_DAYS[frequency];
    if (days == null) { days = DUP_DEFAULT_DAYS; }
    return Math.abs(daysBetween(dateA, dateB)) <= days;
  }

  function incomeLine(source, amount) {
    return source + ", " + formatMoney(amount);
  }

  // A manual income is about to be saved. Looks at real entries a recurring rule already
  // added (only dates that have arrived) and at active rules that will add one later.
  // A scheduled entry is described as scheduled: it is never counted as received.
  function findDuplicatesForManualIncome(amount, source, date, ignoreId) {
    var today = todayStr();
    var found = [];
    data.transactions.forEach(function (t) {
      if (t.type !== "income" || !t.recurringId || t.id === ignoreId) { return; }
      if (t.amount !== amount || t.date > today || !sameSource(t.source, source)) { return; }
      var rule = findById(data.recurring, t.recurringId);
      if (sameIncomeWindow(rule ? rule.frequency : "", t.date, date)) {
        found.push(incomeLine(t.source, t.amount) + ", received " + formatDate(t.date) +
          " (added by a recurring rule)");
      }
    });
    data.recurring.forEach(function (r) {
      if (r.type !== "income" || !r.active || r.amount !== amount || !sameSource(r.source, source)) { return; }
      if (sameIncomeWindow(r.frequency, r.nextDate, date)) {
        found.push("Recurring " + frequencyLabel(r.frequency).toLowerCase() + " income: " +
          incomeLine(r.source, r.amount) + ", scheduled for " + formatDate(r.nextDate) +
          " (not received yet)");
      }
    });
    return found;
  }

  // A recurring income rule is about to be saved. Looks for manual incomes (entries not
  // created by a rule) that already happened in the same period as the rule's next date.
  function findDuplicatesForRecurringIncome(amount, source, frequency, nextDate) {
    var today = todayStr();
    var found = [];
    data.transactions.forEach(function (t) {
      if (t.type !== "income" || t.recurringId || t.date > today) { return; }
      if (t.amount !== amount || !sameSource(t.source, source)) { return; }
      if (sameIncomeWindow(frequency, nextDate, t.date)) {
        found.push(incomeLine(t.source, t.amount) + ", added manually on " + formatDate(t.date));
      }
    });
    return found;
  }

  // Shows the Add Anyway / Cancel question. Cancel leaves the form open so nothing is lost.
  function askAboutDuplicateIncome(cfg) {
    openConfirm({
      title: cfg.title || "Possible duplicate income",
      message: cfg.message,
      summary: cfg.summary,
      removesTitle: cfg.matchesTitle,
      removes: cfg.matches,
      keepsTitle: "Nothing changes automatically",
      keeps: [
        "Your existing records are not deleted, merged or changed",
        "Add Anyway saves this as a separate income"
      ],
      confirmLabel: "Add Anyway",
      confirmClass: "btn-primary",
      cancelLabel: "Cancel",
      onConfirm: cfg.onConfirm
    });
  }

  /* ---------------------------------------------------------
     9. CALCULATIONS (Safe-to-Spend and the rest)
     --------------------------------------------------------- */
  // What one goal sets aside this period: already saved this period + still planned
  function goalReserve(g, period, today) {
    var contributed = 0;
    g.contributions.forEach(function (c) {
      if (c.date >= period.start && c.date <= today) {
        contributed += c.amount;
      }
    });
    var remainingTarget = Math.max(g.target - g.saved, 0);
    var planRemaining = Math.min(Math.max((g.monthlyPlan || 0) - contributed, 0), remainingTarget);
    return contributed + planRemaining;
  }

  function computeStats() {
    var today = todayStr();
    var period = getPeriod(today, data.settings.monthStartDay);
    var income = 0;
    var spent = 0;
    var spentByCategory = {};

    data.transactions.forEach(function (t) {
      if (t.date < period.start || t.date > period.end || t.date > today) {
        return;
      }
      if (t.type === "income") {
        income += t.amount;
      } else {
        spent += t.amount;
        spentByCategory[t.categoryId] = (spentByCategory[t.categoryId] || 0) + t.amount;
      }
    });

    // Unpaid bills only (paid bills are already inside "spent")
    var unpaidDue = 0;
    data.bills.forEach(function (b) {
      if (!b.paid && b.dueDate <= period.end) {
        unpaidDue += b.amount;
      }
    });

    // Savings for this period only: already set aside + still planned
    var savingsReserve = 0;
    data.goals.forEach(function (g) {
      savingsReserve += goalReserve(g, period, today);
    });

    var available = income - spent - unpaidDue - savingsReserve;
    var daysLeft = daysBetween(today, period.end) + 1;
    var safePerDay = Math.floor(Math.max(available, 0) / daysLeft);

    var budgets = data.budgets.map(function (b) {
      var spentInCategory = spentByCategory[b.categoryId] || 0;
      var pct = b.limit > 0 ? (spentInCategory / b.limit) * 100 : 0;
      return {
        id: b.id,
        categoryId: b.categoryId,
        name: categoryName(b.categoryId),
        limit: b.limit,
        spent: spentInCategory,
        remaining: b.limit - spentInCategory,
        pct: pct,
        status: pct >= 100 ? "over" : pct >= 80 ? "warn" : "ok"
      };
    });

    return {
      today: today,
      period: period,
      income: income,
      spent: spent,
      left: income - spent,
      unpaidDue: unpaidDue,
      savingsReserve: savingsReserve,
      available: available,
      daysLeft: daysLeft,
      safePerDay: safePerDay,
      budgets: budgets
    };
  }

  /* ---------------------------------------------------------
     10. RENDER HELPERS
     --------------------------------------------------------- */
  function btn(label, action, cls, id) {
    return '<button type="button" class="btn ' + cls + '" data-action="' + action + '"' +
      (id ? ' data-id="' + esc(id) + '"' : "") + ">" + esc(label) + "</button>";
  }

  function emptyState(title, text, buttonHTML) {
    return '<div class="empty-state"><p class="empty-title">' + esc(title) + "</p>" +
      '<p class="empty-text">' + esc(text) + "</p>" + (buttonHTML || "") + "</div>";
  }

  function progressHTML(pct, status) {
    var width = Math.max(0, Math.min(100, pct));
    return '<div class="progress" role="progressbar" aria-valuemin="0" aria-valuemax="100" aria-valuenow="' +
      Math.round(width) + '"><div class="progress-bar ' + status + '" style="width:' + width + '%"></div></div>';
  }

  function compareTransactions(a, b) {
    if (a.date !== b.date) {
      return a.date < b.date ? 1 : -1;
    }
    return (b.createdAt || 0) - (a.createdAt || 0);
  }

  function transactionTitle(t) {
    if (t.type === "income") {
      return t.source;
    }
    if (t.billId) {
      var bill = findById(data.bills, t.billId);
      if (bill) {
        return bill.name;
      }
    }
    if (t.debtId) {
      var debt = findById(data.debts, t.debtId);
      if (debt) { return debt.name; }
    }
    return categoryName(t.categoryId);
  }

  function transactionRowHTML(t) {
    var isIncome = t.type === "income";
    var title = transactionTitle(t);
    var subParts = [formatDate(t.date)];
    if (!isIncome && title !== categoryName(t.categoryId)) {
      subParts.push(categoryName(t.categoryId));
    }
    if (t.method) {
      subParts.push(t.method);
    }
    if (t.recurringId) {
      subParts.push("Recurring");
    }
    var actions;
    if (t.debtId) {
      actions = '<span class="badge badge-muted">Debt payment</span>';
    } else if (t.billId) {
      actions = '<span class="badge badge-muted">Paid bill</span>' +
        btn("Delete", "delete-transaction", "btn-ghost btn-small btn-danger-text", t.id);
    } else {
      actions = btn("Edit", "edit-transaction", "btn-ghost btn-small", t.id) +
        btn("Delete", "delete-transaction", "btn-ghost btn-small btn-danger-text", t.id);
    }
    return '<div class="row"><div class="row-main"><div class="row-title">' + esc(title) + "</div>" +
      '<div class="row-sub">' + esc(subParts.join(" \u00B7 ")) + "</div></div>" +
      '<div class="row-amount ' + (isIncome ? "income" : "expense") + '">' + (isIncome ? "+" : "-") +
      formatMoney(t.amount) + "</div>" +
      '<div class="row-actions">' + actions + "</div></div>";
  }

  function billDueInfo(b, today) {
    if (b.paid) {
      return { label: "Paid", cls: "badge-ok" };
    }
    var diff = daysBetween(today, b.dueDate);
    if (diff < 0) {
      return { label: "Past due by " + plural(-diff, "day"), cls: "badge-over" };
    }
    if (diff === 0) {
      return { label: "Due today", cls: "badge-warn" };
    }
    if (diff <= 7) {
      return { label: "Due in " + plural(diff, "day"), cls: "badge-warn" };
    }
    return { label: "Due " + formatDate(b.dueDate), cls: "badge-muted" };
  }

  /* ---------------------------------------------------------
     11. RENDER: HOME
     --------------------------------------------------------- */
  function greetingText() {
    var hour = new Date().getHours();
    var part = hour < 12 ? "Good morning" : hour < 18 ? "Good afternoon" : "Good evening";
    var name = data.settings.name;
    return part + (name ? ", " + name : "") + ".";
  }

  // Calm reminders for unpaid bills. Shown only while the app is open.
  function renderReminders(stats) {
    var lines = [];
    var notes = [];
    data.bills.filter(function (b) { return !b.paid; }).sort(function (a, b) {
      return a.dueDate < b.dueDate ? -1 : 1;
    }).forEach(function (b) {
      var d = daysBetween(stats.today, b.dueDate);
      if (d > 7) { return; }
      var when = d < 0 ? "past due by " + plural(-d, "day") : d === 0 ? "due today" : "due in " + plural(d, "day");
      var line = b.name + " is " + when + ".";
      lines.push(line);
      var stage = d === 7 ? "7" : d === 3 ? "3" : d === 0 ? "0" : d < 0 ? "over:" + stats.today : "";
      if (stage) { notes.push({ key: b.id + ":" + stage, text: line }); }
    });
    $("reminders").innerHTML = lines.map(function (l) { return "<p>" + esc(l) + "</p>"; }).join("");
    $("reminders").hidden = lines.length === 0;
    sendBrowserReminders(notes);
  }

  function lsGet(k) { try { return localStorage.getItem(k); } catch (e) { return null; } }
  function lsSet(k, v) { try { localStorage.setItem(k, v); } catch (e) { /* ignore */ } }
  function notifyEnabled() {
    return typeof Notification !== "undefined" && Notification.permission === "granted" && lsGet("monetra.notify") === "1";
  }

  // Optional browser reminders: only after the user turns them on, only while the app is open, once per bill and stage
  function sendBrowserReminders(notes) {
    if (!notifyEnabled() || !storageWorks) { return; }
    var sent = {};
    try { sent = JSON.parse(lsGet("monetra.notified") || "{}"); } catch (e) { sent = {}; }
    var changed = false;
    notes.forEach(function (n) {
      if (sent[n.key]) { return; }
      sent[n.key] = todayStr();
      changed = true;
      try { new Notification("Monetra", { body: n.text }); } catch (e) { /* ignore */ }
    });
    Object.keys(sent).forEach(function (k) {
      if (daysBetween(sent[k], todayStr()) > 30) { delete sent[k]; changed = true; }
    });
    if (changed) { lsSet("monetra.notified", JSON.stringify(sent)); }
  }

  // Calm overview shown once when someone returns after a few days. No counts of missed days.
  function renderCatchUp(stats) {
    var box = $("catchup");
    if (!catchUpActive || (data.transactions.length === 0 && data.bills.length === 0)) { box.hidden = true; return; }
    var soon = [];
    var over = [];
    data.bills.forEach(function (b) {
      if (b.paid) { return; }
      var d = daysBetween(stats.today, b.dueDate);
      if (d < 0) { over.push(b.name); } else if (d <= 7) { soon.push(b.name + " (" + (d === 0 ? "today" : "in " + plural(d, "day")) + ")"); }
    });
    var hasIncome = stats.income > 0;
    box.innerHTML = "<h2>Welcome back</h2><p>Here is where things stand today.</p>" +
      "<p><strong>Safe to Spend:</strong> " + esc(hasIncome ? formatMoney(stats.safePerDay) + " a day" : "--") + "</p>" +
      "<p><strong>Remaining:</strong> " + esc(hasIncome ? formatMoney(Math.max(stats.available, 0)) : "--") + "</p>" +
      (soon.length ? "<p><strong>Coming up:</strong> " + esc(soon.join(", ")) + "</p>" : "") +
      (over.length ? "<p><strong>Past due:</strong> " + esc(over.join(", ")) + "</p>" : "") +
      btn("Got it", "dismiss-catchup", "btn-secondary btn-small");
    box.hidden = false;
  }

  function renderHome(stats) {
    renderCatchUp(stats);
    renderReminders(stats);
    $("home-greeting").innerHTML = '<span class="greet-line">' + esc(greetingText()) + '</span><span class="greet-tag">Manage Money. Find Your Focus.</span>';

    var hasIncome = stats.income > 0;
    var hasActivity = stats.income > 0 || stats.spent > 0 || stats.unpaidDue > 0 || stats.savingsReserve > 0;
    // Income dated before this budget period is saved, but belongs to an earlier period
    var incomeBeforePeriod = data.transactions.some(function (t) { return t.type === "income" && t.date < stats.period.start; });

    $("safe-to-spend-amount").textContent = formatMoney(stats.safePerDay);
    $("safe-to-spend-total").textContent = formatMoney(Math.max(stats.available, 0));
    $("safe-to-spend-days").textContent = String(stats.daysLeft);

    // Short messages. With no income, nothing is compared against a plan.
    var note;
    if (!hasActivity) {
      note = incomeBeforePeriod
        ? "Your income is dated before this period (" + formatPeriod(stats.period) + "), so it is not counted."
        : "Add your income to see your daily amount.";
    } else if (!hasIncome) {
      note = "No income recorded for this period.";
    } else if (stats.available < 0) {
      note = "Over plan by " + formatMoney(-stats.available) + ".";
    } else if (stats.available === 0) {
      note = "Nothing left to spend this period.";
    } else {
      note = "Spread evenly over the remaining days.";
    }
    $("safe-to-spend-note").textContent = note;
    if (!hasActivity || !hasIncome) {
      $("safe-to-spend-amount").textContent = "--";
      $("safe-to-spend-total").textContent = "--";
    }

    var totalText = hasIncome ? formatMoney(stats.available) : "--";
    var perDayText = hasIncome ? formatMoney(stats.safePerDay) : "--";
    $("safe-to-spend-breakdown").innerHTML =
      '<div class="breakdown-row"><span>Income received</span><span>+' + formatMoney(stats.income) + "</span></div>" +
      '<div class="breakdown-row"><span>Spent so far</span><span>-' + formatMoney(stats.spent) + "</span></div>" +
      '<div class="breakdown-row"><span>Unpaid bills due by period end</span><span>-' + formatMoney(stats.unpaidDue) + "</span></div>" +
      '<div class="breakdown-row"><span>Savings set aside this period</span><span>-' + formatMoney(stats.savingsReserve) + "</span></div>" +
      '<div class="breakdown-row total"><span>Total safe to spend</span><span>' + totalText + "</span></div>" +
      '<div class="breakdown-row"><span>Days left (today included)</span><span>' + stats.daysLeft + "</span></div>" +
      '<div class="breakdown-row total"><span>Safe per day</span><span>' + perDayText + "</span></div>" +
      '<p class="breakdown-note">Only money that has already arrived is counted. Paid bills are already inside "Spent", so they are never counted twice. Savings count only this period\'s plan.</p>';

    $("period-label").textContent = "Budget period: " + formatPeriod(stats.period);
    $("summary-income").textContent = formatMoney(stats.income);
    $("summary-spent").textContent = formatMoney(stats.spent);
    $("summary-left").textContent = hasIncome ? formatMoney(stats.left) : "--";
    $("summary-left").parentNode.classList.toggle("is-negative", hasIncome && stats.left < 0);
    if (stats.income > 0) {
      var sp = stats.spent / stats.income * 100;
      $("summary-progress").innerHTML = '<p class="field-hint">Spending progress: ' + Math.round(sp) + "% of income spent</p>" + progressHTML(sp, sp >= 100 ? "warn" : "");
    } else if (incomeBeforePeriod) {
      $("summary-progress").innerHTML = '<p class="field-hint">Income dated before this budget period is not counted here. You can find it in Money, under Search Transactions, or change the Day Start in More.</p>';
    } else {
      $("summary-progress").innerHTML = "";
    }

    var unpaid = data.bills.filter(function (b) { return !b.paid; })
      .sort(function (a, b) { return a.dueDate < b.dueDate ? -1 : 1; });
    if (unpaid.length === 0) {
      $("upcoming-bills-list").innerHTML = emptyState(
        "No unpaid bills",
        "Nice and quiet. Add a bill to see it here before it is due.",
        btn("Add Bill", "add-bill", "btn-add btn-small btn-secondary")
      );
    } else {
      $("upcoming-bills-list").innerHTML = unpaid.slice(0, 4).map(function (b) {
        var info = billDueInfo(b, stats.today);
        return '<div class="row"><div class="row-main"><div class="row-title">' + esc(b.name) + "</div>" +
          '<div class="row-sub"><span class="badge ' + info.cls + '">' + esc(info.label) + "</span></div></div>" +
          '<div class="row-amount">' + formatMoney(b.amount) + "</div></div>";
      }).join("");
    }

    if (data.goals.length === 0) {
      $("home-goals-list").innerHTML = emptyState(
        "No savings goals yet",
        "Start with one small goal, like an emergency fund.",
        btn("Add Goal", "add-goal", "btn-add btn-small btn-secondary")
      );
    } else {
      $("home-goals-list").innerHTML = data.goals.slice(0, 3).map(function (g) {
        var pct = g.target > 0 ? (g.saved / g.target) * 100 : 0;
        return '<div class="mini"><div class="mini-head"><span>' + esc(g.name) + "</span><span>" +
          formatMoney(g.saved) + " of " + formatMoney(g.target) + "</span></div>" +
          progressHTML(pct, "") + "</div>";
      }).join("");
    }

    if (stats.budgets.length === 0) {
      $("home-budgets-list").innerHTML = emptyState(
        "No budgets yet",
        "Set a monthly limit for a category to see how much is left.",
        btn("Add Budget", "add-budget", "btn-add btn-small btn-secondary")
      );
    } else {
      $("home-budgets-list").innerHTML = stats.budgets.slice().sort(function (a, b) {
        return b.pct - a.pct;
      }).slice(0, 4).map(function (b) {
        var rightText = b.remaining >= 0 ? formatMoney(b.remaining) + " left" : "Over by " + formatMoney(-b.remaining);
        return '<div class="mini"><div class="mini-head"><span>' + esc(b.name) + "</span><span>" +
          esc(rightText) + "</span></div>" + progressHTML(b.pct, b.status === "ok" ? "" : b.status) + "</div>";
      }).join("");
    }
  }

  /* ---------------------------------------------------------
     12. RENDER: MONEY (Income, Expenses, Search)
     --------------------------------------------------------- */
  function emptyAddBtn(type) {
    var any = data.transactions.some(function (t) { return t.type === type; });
    return btn((any ? "Add " : "Add First ") + (type === "income" ? "Income" : "Expense"),
      type === "income" ? "add-income" : "add-expense", "btn-add btn-small btn-secondary");
  }

  function renderPeriodList(type, stats) {
    var rows = data.transactions.filter(function (t) {
      return t.type === type && t.date >= stats.period.start && t.date <= stats.period.end && t.date <= stats.today;
    }).sort(compareTransactions);

    var total = type === "income" ? stats.income : stats.spent;
    var label = type === "income" ? "income" : "expenses";

    if (rows.length === 0) {
      // Income can exist but be dated outside this budget period: say so instead of looking lost
      var datedElsewhere = type === "income" && data.transactions.some(function (t) { return t.type === "income"; });
      return emptyState(
        "No " + label + " this period yet",
        type === "income"
          ? (datedElsewhere
            ? "Your income is dated outside this budget period. Use Search Transactions below to find it."
            : "Record money you received and it will show up here.")
          : "Record what you spent and it will show up here.",
        emptyAddBtn(type)
      );
    }

    var html = '<p class="list-summary"><span>This period (' + esc(formatPeriod(stats.period)) +
      ")</span><strong>" + formatMoney(total) + "</strong></p>";
    html += rows.slice(0, MAX_LIST_ROWS).map(transactionRowHTML).join("");
    if (rows.length > MAX_LIST_ROWS) {
      html += '<p class="muted">Showing the latest ' + MAX_LIST_ROWS + ". Use Search Transactions below to find the rest.</p>";
    }
    return html;
  }

  // Recurring entries are no longer managed on a screen. Existing rules keep working
  // in the background (processRecurring), so old data is never lost.
  function renderRecurring() {
    var list = $("recurring-list");
    if (!list) { return; }
    if (data.recurring.length === 0) {
      list.innerHTML = emptyState(
        "No recurring entries yet",
        "Add one for things that repeat, like a salary or a monthly subscription."
      );
      return;
    }

    var sorted = data.recurring.slice().sort(function (a, b) {
      if (a.active !== b.active) { return a.active ? -1 : 1; }
      return a.nextDate < b.nextDate ? -1 : 1;
    });

    list.innerHTML = sorted.map(function (r) {
      var isIncome = r.type === "income";
      var title = isIncome ? r.source : categoryName(r.categoryId);
      var nextText = r.active ? "Next: " + formatDate(r.nextDate) : "Paused";
      var parts = [frequencyLabel(r.frequency), nextText];
      if (!isIncome && r.method) { parts.push(r.method); }
      return '<div class="row"><div class="row-main"><div class="row-title">' + esc(title) + "</div>" +
        '<div class="row-sub">' + esc(parts.join(" \u00B7 ")) + "</div>" +
        '<div class="row-sub"><span class="badge ' + (r.active ? "badge-ok" : "badge-muted") + '">' +
        (r.active ? "Active" : "Paused") + "</span> <span class=\"badge badge-muted\">" +
        (isIncome ? "Income" : "Expense") + "</span></div></div>" +
        '<div class="row-amount ' + (isIncome ? "income" : "expense") + '">' + (isIncome ? "+" : "-") +
        formatMoney(r.amount) + "</div>" +
        '<div class="row-actions">' +
        btn(r.active ? "Pause" : "Resume", "toggle-recurring", "btn-secondary btn-small", r.id) +
        btn("Edit", "edit-recurring", "btn-ghost btn-small", r.id) +
        btn("Delete", "delete-recurring", "btn-ghost btn-small btn-danger-text", r.id) +
        "</div></div>";
    }).join("");
  }

  // One search box. Nothing is listed until the person types. Matches income and expenses.
  function renderHistory() {
    var input = $("history-search");
    var list = $("history-list");
    if (!input || !list) { return; }
    var query = input.value.trim().toLowerCase();

    if (data.transactions.length === 0) {
      list.innerHTML = emptyState(
        "No transactions yet",
        "Income and expenses you add will be searchable here."
      );
      return;
    }

    if (!query) {
      list.innerHTML = emptyState(
        "Search your transactions",
        "Type a name, category or amount to find income or expenses."
      );
      return;
    }

    var rows = data.transactions.filter(function (t) {
      var haystack = [
        transactionTitle(t), t.type, t.method || "",
        t.type === "expense" ? categoryName(t.categoryId) : "",
        (t.amount / 100).toFixed(2), String(t.amount / 100), formatMoney(t.amount),
        t.date, formatDate(t.date)
      ].join(" ").toLowerCase();
      return haystack.indexOf(query) !== -1;
    }).sort(compareTransactions);

    if (rows.length === 0) {
      list.innerHTML = emptyState(
        "No matching transactions",
        "Try a different name, category or amount."
      );
      return;
    }

    var html = rows.slice(0, MAX_HISTORY_ROWS).map(transactionRowHTML).join("");
    if (rows.length > MAX_HISTORY_ROWS) {
      html += '<p class="muted">Showing the latest ' + MAX_HISTORY_ROWS + ". Narrow your search to see the rest.</p>";
    }
    list.innerHTML = html;
  }

  function renderMoney(stats) {
    $("income-list").innerHTML = renderPeriodList("income", stats);
    $("expenses-list").innerHTML = renderPeriodList("expense", stats);
    $("expenses-tools").hidden = expensesDeletableInBulk().length === 0;
    $("income-tools").hidden = incomeRecords().length === 0;
    renderRecurring();
    renderHistory();
  }

  /* ---------------------------------------------------------
     13. RENDER: BUDGETS (cards, monthly review, alerts)
     --------------------------------------------------------- */
  function budgetBadge(b) {
    if (b.status === "over") {
      return { label: "Limit reached", cls: "badge-over" };
    }
    if (b.status === "warn") {
      return { label: "Heads up", cls: "badge-warn" };
    }
    return { label: "On track", cls: "badge-ok" };
  }

  function sumPeriod(from, to) {
    var r = { income: 0, spent: 0, count: 0, byCat: {} };
    data.transactions.forEach(function (t) {
      if (t.date < from || t.date > to) { return; }
      if (t.type === "income") { r.income += t.amount; return; }
      r.spent += t.amount;
      r.count += 1;
      r.byCat[t.categoryId] = (r.byCat[t.categoryId] || 0) + t.amount;
    });
    return r;
  }

  function renderReview(stats) {
    var per = stats.period;
    if (reviewOffset < 0) { per = getPeriod(addMonths(stats.period.start, reviewOffset, data.settings.monthStartDay), data.settings.monthStartDay); }
    var to = per.end < stats.today ? per.end : stats.today;
    $("review-period").textContent = formatPeriod(per);
    $("review-prev").disabled = !data.transactions.some(function (t) { return t.date < per.start; });
    $("review-next").disabled = reviewOffset >= 0;
    var cur = sumPeriod(per.start, to);
    if (cur.income === 0 && cur.spent === 0) {
      $("review-content").innerHTML = emptyState(
        "Nothing to review yet",
        incomeRecords().length === 0
          ? "No income recorded yet. Add your income and expenses and your overview appears here."
          : "No income or expenses in this period yet. Your overview appears once you add some.",
        btn("Add Income", "add-income", "btn-add btn-small btn-secondary") + " " +
        btn("Add Expense", "add-expense", "btn-add btn-small btn-secondary")
      );
      return;
    }
    var noIncome = cur.income === 0;
    var remaining = cur.income - cur.spent;
    var topId = null;
    Object.keys(cur.byCat).forEach(function (id) {
      if (topId === null || cur.byCat[id] > cur.byCat[topId]) { topId = id; }
    });
    var planned = 0;
    var budgeted = 0;
    stats.budgets.forEach(function (b) { planned += b.limit; budgeted += cur.byCat[b.categoryId] || 0; });

    // With no income there is nothing to compare spending with, so no "Beyond income" figure is shown.
    var html = '<p class="review-lead">Your spending overview is ready.</p>' +
      '<div class="summary-row">' +
      "<div><span>Income</span><strong>" + (noIncome ? "None recorded" : formatMoney(cur.income)) + "</strong></div>" +
      "<div><span>Spending</span><strong>" + formatMoney(cur.spent) + "</strong></div>" +
      '<div class="' + (!noIncome && remaining < 0 ? "is-negative" : "") + '"><span>' +
      (noIncome ? "Remaining" : (remaining < 0 ? "Beyond income" : "Remaining")) + "</span><strong>" +
      (noIncome ? "--" : formatMoney(Math.abs(remaining))) + "</strong></div></div>";

    if (noIncome) {
      html += '<p class="review-line">No income recorded for this period. ' +
        btn("Add Income", "add-income", "btn-add btn-small btn-secondary") + "</p>";
    }
    if (topId !== null && cur.spent > 0) {
      html += '<p class="review-line">Here\'s where your money went. Most of it went to <strong>' + esc(categoryName(topId)) +
        "</strong>: " + formatMoney(cur.byCat[topId]) + " (" + Math.round(cur.byCat[topId] / cur.spent * 100) + "% of your spending).</p>";
    }
    if (planned > 0) {
      var pct = budgeted / planned * 100;
      html += '<p class="review-line">Budget usage: <strong>' + Math.round(pct) + "%</strong> (" + formatMoney(budgeted) +
        " of " + formatMoney(planned) + " in budgeted categories)</p>" + progressHTML(pct, pct >= 100 ? "over" : pct >= 80 ? "warn" : "") + (pct < 100 ? '<p class="review-line">You\'ve made progress toward your budget.</p>' : "");
    }

    // Compare with the same number of days last period, and only when both periods have expenses
    var prev = getPeriod(addDays(per.start, -1), data.settings.monthStartDay);
    var prevTo = addDays(prev.start, daysBetween(per.start, to));
    if (prevTo > prev.end) { prevTo = prev.end; }
    var before = sumPeriod(prev.start, prevTo);
    if (before.count > 0 && cur.count > 0) {
      var diff = cur.spent - before.spent;
      html += '<p class="review-line">' + (diff < 0
        ? "You're making progress: " + formatMoney(-diff) + " less spent than over the same days last period."
        : diff > 0
          ? "Spending is " + formatMoney(diff) + " higher than over the same days last period. No pressure, this is just your overview."
          : "Spending matches the same days last period.") + "</p>";
    }
    $("review-content").innerHTML = html;
  }

  function renderBudgets(stats) {
    renderReview(stats);

    if (stats.budgets.length === 0) {
      $("budgets-list").innerHTML = emptyState(
        "No category budgets yet",
        "A budget is a monthly limit for one category, so you can see what is left.",
        btn("Create Budget", "add-budget", "btn-add btn-small btn-secondary")
      );
      $("alerts-list").innerHTML = emptyState("No alerts", "Alerts appear here when a budget reaches 80% or 100%.");
      return;
    }

    var sorted = stats.budgets.slice().sort(function (a, b) {
      return a.name.toLowerCase() < b.name.toLowerCase() ? -1 : 1;
    });

    $("budgets-list").innerHTML = sorted.map(function (b) {
      var badge = budgetBadge(b);
      var leftText = b.remaining >= 0
        ? "Left<strong>" + formatMoney(b.remaining) + "</strong>"
        : "Over by<strong>" + formatMoney(-b.remaining) + "</strong>";
      return '<div class="item"><div class="item-head"><div><div class="item-title">' + esc(b.name) + "</div>" +
        '<div class="item-sub">Monthly limit ' + formatMoney(b.limit) + '</div></div><span class="badge ' + badge.cls + '">' +
        esc(badge.label) + "</span></div>" + progressHTML(b.pct, b.status === "ok" ? "" : b.status) +
        '<div class="item-stats"><span>Spent<strong>' + formatMoney(b.spent) + "</strong></span><span>" + leftText +
        "</span><span>Used<strong>" + Math.round(b.pct) + "%</strong></span></div>" +
        '<div class="item-actions">' + btn("Edit", "edit-budget", "btn-ghost btn-small", b.id) +
        btn("Delete", "delete-budget", "btn-ghost btn-small btn-danger-text", b.id) + "</div></div>";
    }).join("");

    var alerts = stats.budgets.filter(function (b) { return b.status !== "ok"; })
      .sort(function (a, b) { return b.pct - a.pct; });

    if (alerts.length === 0) {
      $("alerts-list").innerHTML = emptyState("No alerts", "All your budgets are under 80%. You are doing fine.");
    } else {
      $("alerts-list").innerHTML = alerts.map(function (b) {
        var text;
        if (b.remaining < 0) {
          text = b.name + " has gone past its budget by " + formatMoney(-b.remaining) + ". You can raise the limit if it was too tight.";
        } else if (b.status === "over") {
          text = "You have reached your limit for " + b.name + ".";
        } else {
          text = b.name + " is at " + Math.round(b.pct) + "% of its budget. A gentle heads up, most of it is used.";
        }
        return '<div class="alert-item ' + (b.status === "over" ? "alert-over" : "alert-warn") + '">' + esc(text) + "</div>";
      }).join("");
    }
  }

  /* ---------------------------------------------------------
     14. RENDER: BILLS
     --------------------------------------------------------- */
  function renderBills(stats) {
    if (data.bills.length === 0) {
      $("bills-list").innerHTML = emptyState(
        "No bills or subscriptions yet",
        "Bills and subscriptions repeat. Add one to see it before it is due.",
        btn("Add First Bill", "add-bill", "btn-add btn-small btn-secondary")
      );
      return;
    }

    var sorted = data.bills.slice().sort(function (a, b) {
      if (a.paid !== b.paid) { return a.paid ? 1 : -1; }
      if (a.paid) { return a.dueDate < b.dueDate ? 1 : -1; }
      return a.dueDate < b.dueDate ? -1 : 1;
    });

    $("bills-list").innerHTML = sorted.map(function (b) {
      var info = billDueInfo(b, stats.today);
      var missingBadge = b.paid && !billPaymentTx(b)
        ? ' <span class="badge badge-warn">Payment record missing</span>' : "";
      return '<div class="row"><div class="row-main"><div class="row-title">' + esc(b.name) + "</div>" +
        '<div class="row-sub">Due ' + esc(formatDate(b.dueDate)) + " &middot; " + esc(categoryName(b.categoryId)) + "</div>" +
        '<div class="row-sub"><span class="badge ' + info.cls + '">' + esc(info.label) + "</span>" + missingBadge + "</div></div>" +
        '<div class="row-amount">' + formatMoney(b.amount) + "</div>" +
        '<div class="row-actions">' +
        btn(b.paid ? "Mark unpaid" : "Mark paid", "toggle-bill", "btn-secondary btn-small", b.id) +
        btn("Edit", "edit-bill", "btn-ghost btn-small", b.id) +
        btn("Delete", "delete-bill", "btn-ghost btn-small btn-danger-text", b.id) +
        "</div></div>";
    }).join("");
  }

  /* ---------------------------------------------------------
     15. RENDER: GOALS
     --------------------------------------------------------- */
  /* ---------------------------------------------------------
     Debt payoff. A payment is saved in its debt AND as one linked expense
     (debtId + debtPaymentId), so Safe to Spend and monthly totals count it
     exactly once. Debt balances themselves are never deducted.
     --------------------------------------------------------- */
  function debtPaidTotal(d, exceptId) {
    var total = d.paidBefore || 0;
    d.payments.forEach(function (p) { if (p.id !== exceptId) { total += p.amount; } });
    return total;
  }

  // Interest rate is informational only. It is never used in any balance or payment calculation.
  // Stored as a plain number of percent (5.5 = 5.5%), or null when not set.
  function isValidRate(v) {
    return typeof v === "number" && isFinite(v) && v >= 0 && v <= 100;
  }

  // Returns null for an empty field, a number for a valid rate, or undefined for an invalid entry.
  function parseInterestRate(text) {
    var cleaned = String(text).replace(/\s/g, "");
    if (cleaned === "") { return null; }
    cleaned = cleaned.replace(/%$/, "");
    if (!/^(\d+(\.\d{1,2})?|\.\d{1,2})$/.test(cleaned)) { return undefined; }
    var n = parseFloat(cleaned);
    return isValidRate(n) ? n : undefined;
  }

  function formatRate(v) {
    return isValidRate(v) ? String(v) + "%" : "Not set";
  }

  function debtTx(p) {
    for (var i = 0; i < data.transactions.length; i++) {
      if (data.transactions[i].debtPaymentId === p.id) { return data.transactions[i]; }
    }
    return null;
  }

  function debtPayBtn(label, action, cls, d, p) {
    return '<button type="button" class="btn ' + cls + '" data-action="' + action + '" data-id="' + esc(d.id) + '" data-pid="' + esc(p.id) + '">' + esc(label) + "</button>";
  }

  function renderDebts() {
    $("debt-summary").hidden = data.debts.length === 0;
    if (data.debts.length === 0) {
      $("debts-list").innerHTML = emptyState(
        "No debts added",
        "Track what you owe and watch the balance go down. This is optional.",
        btn("Add First Debt", "add-debt", "btn-add btn-small btn-secondary")
      );
      return;
    }
    var original = 0;
    var paid = 0;
    var remaining = 0;
    data.debts.forEach(function (d) {
      var owed = Math.max(d.original - debtPaidTotal(d, ""), 0);
      original += d.original;
      remaining += owed;
      paid += d.original - owed;
    });
    var pct = original > 0 ? Math.min(paid / original * 100, 100) : 0;
    $("debt-summary-body").innerHTML = '<div class="summary-row">' +
      "<div><span>Original Debt</span><strong>" + formatMoney(original) + "</strong></div>" +
      "<div><span>Total Paid</span><strong>" + formatMoney(paid) + "</strong></div>" +
      "<div><span>Remaining</span><strong>" + formatMoney(remaining) + "</strong></div></div>" +
      '<p class="field-hint">Overall progress: ' + Math.round(pct) + "%</p>" + progressHTML(pct, "");

    $("debts-list").innerHTML = data.debts.map(function (d) {
      var owed = Math.max(d.original - debtPaidTotal(d, ""), 0);
      var done = d.original - owed;
      var dpct = d.original > 0 ? Math.min(done / d.original * 100, 100) : 0;
      var rows = [];
      if (d.paidBefore > 0) {
        rows.push('<div class="row"><div class="row-main"><div class="row-title">Paid before using Monetra</div></div><div class="row-amount">' + formatMoney(d.paidBefore) + "</div></div>");
      }
      d.payments.slice().sort(function (a, b) { return a.date < b.date ? 1 : -1; }).forEach(function (p) {
        rows.push('<div class="row"><div class="row-main"><div class="row-title">' + esc(formatDate(p.date)) + '</div></div><div class="row-amount expense">' +
          formatMoney(p.amount) + '</div><div class="row-actions">' + debtPayBtn("Edit", "edit-debt-payment", "btn-ghost btn-small", d, p) +
          debtPayBtn("Delete", "delete-debt-payment", "btn-ghost btn-small btn-danger-text", d, p) + "</div></div>");
      });
      var history = rows.length ? '<details class="debt-history"><summary>Payment history (' + d.payments.length + ")</summary>" + rows.join("") + "</details>" : "";
      return '<div class="item"><div class="item-head"><div class="item-title">' + esc(d.name) + '</div><span class="badge ' +
        (owed === 0 ? "badge-ok" : "badge-muted") + '">' + (owed === 0 ? "Paid off" : Math.round(dpct) + "%") + "</span></div>" +
        progressHTML(dpct, "") +
        '<div class="item-stats"><span>Original<strong>' + formatMoney(d.original) + "</strong></span><span>Paid<strong>" + formatMoney(done) +
        "</strong></span><span>Remaining<strong>" + formatMoney(owed) + "</strong></span><span>Interest Rate<strong>" + esc(formatRate(d.interestRate)) + "</strong></span></div>" + history +
        '<div class="item-actions">' + (owed > 0 ? btn("Record Payment", "pay-debt", "btn-secondary btn-small btn-add", d.id) : "") +
        btn("Edit", "edit-debt", "btn-ghost btn-small", d.id) + btn("Delete", "delete-debt", "btn-ghost btn-small btn-danger-text", d.id) + "</div></div>";
    }).join("");
  }

  function renderGoals(stats) {
    if (data.goals.length === 0) {
      $("goals-list").innerHTML = emptyState(
        "No savings goals yet",
        "A savings goal tracks money you are setting aside. One small goal is a great start.",
        btn("Add First Goal", "add-goal", "btn-add btn-small btn-secondary")
      );
      return;
    }

    $("goals-list").innerHTML = data.goals.map(function (g) {
      var pct = g.target > 0 ? (g.saved / g.target) * 100 : 0;
      var reached = g.saved >= g.target;
      var contributed = 0;
      g.contributions.forEach(function (c) {
        if (c.date >= stats.period.start && c.date <= stats.today) { contributed += c.amount; }
      });
      var planStat = "<span>Monthly plan<strong>" + (g.monthlyPlan > 0 ? formatMoney(g.monthlyPlan) : "Not set") + "</strong></span>";
      var periodStat = g.monthlyPlan > 0 ? "<span>Saved this period<strong>" + formatMoney(contributed) + "</strong></span>" : "";
      return '<div class="item"><div class="item-head"><div class="item-title">' + esc(g.name) + '</div><span class="badge ' +
        (reached ? "badge-ok" : "badge-muted") + '">' + (reached ? "Goal reached" : Math.round(pct) + "%") + "</span></div>" +
        progressHTML(pct, "") +
        '<div class="item-stats"><span>Target<strong>' + formatMoney(g.target) + "</strong></span>" +
        "<span>Saved<strong>" + formatMoney(g.saved) + "</strong></span>" +
        "<span>Remaining<strong>" + formatMoney(Math.max(g.target - g.saved, 0)) + "</strong></span>" +
        planStat + periodStat + "</div>" +
        '<div class="item-actions">' + btn("Add Savings", "contribute-goal", "btn-secondary btn-small btn-add", g.id) +
        btn("Edit", "edit-goal", "btn-ghost btn-small", g.id) +
        btn("Delete", "delete-goal", "btn-ghost btn-small btn-danger-text", g.id) + "</div></div>";
    }).join("");
  }

  /* ---------------------------------------------------------
     16. RENDER: MORE (settings)
     --------------------------------------------------------- */
  function renderMore() {
    var counts = {};
    function bump(id, kind) {
      counts[id] = counts[id] || { expense: 0, bill: 0, budget: 0, recurring: 0 };
      counts[id][kind] += 1;
    }
    data.transactions.forEach(function (t) { if (t.type === "expense") { bump(t.categoryId, "expense"); } });
    data.bills.forEach(function (b) { bump(b.categoryId, "bill"); });
    data.budgets.forEach(function (b) { bump(b.categoryId, "budget"); });
    data.recurring.forEach(function (r) { if (r.type === "expense") { bump(r.categoryId, "recurring"); } });

    if (!$("categories-list")) {
      // The category list is no longer on the page; new categories are added inside the forms.
    } else if (data.categories.length === 0) {
      $("categories-list").innerHTML = emptyState("No categories", "Tap + Add Category to create your first one.");
    } else {
      $("categories-list").innerHTML = sortedCategories().map(function (c) {
        var u = counts[c.id];
        var parts = [];
        if (u && u.expense) { parts.push(plural(u.expense, "expense")); }
        if (u && u.bill) { parts.push(plural(u.bill, "bill")); }
        if (u && u.recurring) { parts.push(u.recurring + (u.recurring === 1 ? " recurring expense" : " recurring expenses")); }
        if (u && u.budget) { parts.push("a budget"); }
        var usage = parts.length ? parts.join(", ") : "Not used yet";
        return '<div class="row"><div class="row-main"><div class="row-title">' + esc(c.name) + "</div>" +
          '<div class="row-sub">' + esc(usage) + "</div></div>" +
          '<div class="row-actions">' + btn("Edit", "edit-category", "btn-ghost btn-small", c.id) +
          (c.name === "Other" ? "" : btn("Delete", "delete-category", "btn-ghost btn-small btn-danger-text", c.id)) + "</div></div>";
      }).join("");
    }
  }

  function fillSettingsForm() {
    // The name field was removed from More. The saved name is kept untouched.
    if ($("settings-name")) { $("settings-name").value = data.settings.name; }
    $("settings-currency").value = data.settings.currency;
    $("settings-day").value = String(data.settings.monthStartDay);
  }

  // Applies Focus Mode, Larger Text and Reduced Motion. Reduced Motion follows the device until the user chooses.
  function applyPreferences() {
    var st = data.settings;
    var root = document.documentElement;
    var osReduce = !!(window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches);
    root.classList.toggle("large-text", st.largeText);
    root.classList.toggle("reduce-motion", st.reducedMotion === null ? osReduce : st.reducedMotion);
    document.body.classList.toggle("focus-mode", st.focusMode);
    $("focus-toggle").textContent = "Focus Mode: " + (st.focusMode ? "On" : "Off");
    $("focus-toggle").setAttribute("aria-pressed", String(st.focusMode));
    if ($("pref-focus")) { $("pref-focus").checked = st.focusMode; }
    if ($("pref-large")) { $("pref-large").checked = st.largeText; }
    if ($("pref-motion")) { $("pref-motion").checked = root.classList.contains("reduce-motion"); }
    if ($("pref-notify")) { $("pref-notify").checked = notifyEnabled(); }
  }

  // Each screen section is drawn on its own, so one failing section can never leave the others out of date
  function safeRun(name, fn) {
    try {
      fn();
    } catch (error) {
      if (window.console && console.error) { console.error("Monetra: could not draw " + name, error); }
    }
  }

  function renderAll() {
    var stats = computeStats();
    lastRenderDay = stats.today;
    safeRun("preferences", applyPreferences);
    safeRun("home", function () { renderHome(stats); });
    safeRun("money", function () { renderMoney(stats); });
    safeRun("budgets", function () { renderBudgets(stats); });
    safeRun("bills", function () { renderBills(stats); });
    safeRun("goals", function () { renderGoals(stats); });
    safeRun("debts", renderDebts);
    safeRun("more", renderMore);
  }

  /* ---------------------------------------------------------
     17. TOAST (message + Undo)
     --------------------------------------------------------- */
  function hideToast() {
    $("toast").hidden = true;
    undoAction = null;
    clearTimeout(toastTimer);
  }

  function showToast(message, undoFn) {
    clearTimeout(toastTimer);
    $("toast-message").textContent = message;
    undoAction = undoFn || null;
    $("toast-undo").hidden = !undoFn;
    $("toast").hidden = false;
    toastTimer = setTimeout(hideToast, undoFn ? UNDO_MS : Math.max(4500, String(message).length * 60));
  }

  // Every change goes through here: add due recurring entries, save, redraw, tell the user
  function commit(message, undoFn) {
    processRecurring();
    saveData();
    renderAll();
    if (message) {
      showToast(message, undoFn);
    }
  }

  // Called when the app is opened again or a new day starts
  function refreshDay() {
    if (!data) { return; }
    if (processRecurring()) {
      saveData();
    }
    renderAll();
  }

  /* ---------------------------------------------------------
     18. FORM POPUP (add / edit)
     --------------------------------------------------------- */
  function fieldHTML(f) {
    var id = "f-" + f.name;
    var value = f.value == null ? "" : f.value;
    var label = '<label for="' + id + '">' + esc(f.label) +
      (f.optional ? ' <span class="optional">(optional)</span>' : "") + "</label>";
    var control;

    if (f.type === "select") {
      control = '<select id="' + id + '"' + (f.disabled ? " disabled" : "") + ">" + f.options.map(function (o) {
        return '<option value="' + esc(o.value) + '"' + (String(o.value) === String(value) ? " selected" : "") + ">" +
          esc(o.label) + "</option>";
      }).join("") + "</select>";
    } else if (f.type === "date") {
      control = '<input id="' + id + '" type="date" value="' + esc(value) + '" min="' + esc(f.min || "2000-01-01") + '"' +
        (f.max ? ' max="' + esc(f.max) + '"' : "") + ">";
    } else {
      var listAttr = f.suggestions && f.suggestions.length ? ' list="dl-' + f.name + '"' : "";
      var modeAttr = (f.type === "money" || f.type === "percent") ? ' inputmode="decimal" autocomplete="off"' : ' autocomplete="off"';
      control = '<input id="' + id + '" type="text"' + modeAttr + listAttr + ' maxlength="' + (f.maxlength || 40) +
        '" value="' + esc(value) + '" placeholder="' + esc(f.placeholder || (f.type === "money" ? "0.00" : "")) + '">';
      if (listAttr) {
        control += '<datalist id="dl-' + f.name + '">' + f.suggestions.map(function (s) {
          return '<option value="' + esc(s) + '">';
        }).join("") + "</datalist>";
      }
    }

    if (f.addCategory) {
      control += '<button type="button" class="btn btn-ghost btn-small btn-add" data-action="inline-category">Add category</button>' +
        '<div class="inline-cat" hidden><input type="text" class="inline-cat-input" maxlength="40" placeholder="New category name" autocomplete="off" aria-label="New category name">' +
        '<button type="button" class="btn btn-small" data-action="inline-category-save" data-for="' + id + '">Add</button></div>';
    }
    var hint = f.hint ? '<p class="field-hint">' + esc(f.hint) + "</p>" : "";
    return '<div class="field">' + label + control + hint + "</div>";
  }

  function showFormError(message) {
    var box = $("form-error");
    box.textContent = message;
    box.hidden = false;
  }

  function openForm(config) {
    currentForm = config;
    formSubmitting = false;
    $("form-submit").disabled = false;
    $("form-title").textContent = config.title;
    $("form-submit").textContent = config.submitLabel || "Save";
    $("form-fields").innerHTML = config.fields.map(fieldHTML).join("");
    $("form-error").hidden = true;

    var dialog = $("form-dialog");
    if (typeof dialog.showModal === "function") {
      if (!dialog.open) { dialog.showModal(); }
    } else {
      dialog.setAttribute("open", "");
    }

    var first = $("form-fields").querySelector("input, select");
    if (first) {
      setTimeout(function () { first.focus(); }, 30);
    }
  }

  function closeForm() {
    var dialog = $("form-dialog");
    if (dialog.open) {
      if (typeof dialog.close === "function") { dialog.close(); } else { dialog.removeAttribute("open"); }
    }
    currentForm = null;
    formSubmitting = false;
    $("form-submit").disabled = false;
    // Fields are cleared so the next form always starts empty (nothing can be sent twice)
    $("form-fields").innerHTML = "";
    $("form-error").hidden = true;
  }

  function saveInlineCategory(btnEl) {
    var wrap = btnEl.parentNode;
    var input = wrap.querySelector("input");
    var name = input.value.trim();
    if (!name) { showFormError("Please type a category name."); return; }
    if (data.categories.some(function (x) { return x.name.toLowerCase() === name.toLowerCase(); })) {
      showFormError("You already have a category with this name."); return;
    }
    var cat = { id: uid(), name: name };
    data.categories.push(cat);
    saveData();
    var select = $(btnEl.getAttribute("data-for"));
    var keep = select.disabled ? "" : select.value;
    var opts = categoryOptions();
    if (select.getAttribute("data-budget") !== null || $("form-title").textContent === "Add Budget") {
      var used = data.budgets.map(function (x) { return x.categoryId; });
      opts = opts.filter(function (o) { return used.indexOf(o.value) === -1; });
    }
    select.innerHTML = opts.map(function (o) { return '<option value="' + esc(o.value) + '">' + esc(o.label) + "</option>"; }).join("");
    select.value = cat.id;
    input.value = "";
    wrap.hidden = true;
    $("form-error").hidden = true;
    renderAll();
    showToast("Category added.");
  }

  function setupFormEvents() {
    $("form-dialog").addEventListener("keydown", function (event) {
      if (event.key === "Enter" && event.target.classList && event.target.classList.contains("inline-cat-input")) {
        event.preventDefault();
        saveInlineCategory(event.target.parentNode.querySelector("button"));
      }
    });

    /* One submit at a time. After a successful save the form closes and its fields are cleared.
       If something goes wrong while the screen is redrawn AFTER the record was saved, the form
       still closes, so the same entry can never be added twice by clicking again.
       Validation errors keep the form open and show the message. */
    $("entry-form").addEventListener("submit", function (event) {
      event.preventDefault();
      if (!currentForm || formSubmitting) { return; }
      formSubmitting = true;
      $("form-submit").disabled = true;

      var outcome = "done";
      try {
        var values = {};
        currentForm.fields.forEach(function (f) {
          var el = $("f-" + f.name);
          values[f.name] = el ? el.value.trim() : "";
        });
        var error = currentForm.onSubmit(values);
        if (error === FORM_PENDING) {
          outcome = "pending";
        } else if (error) {
          showFormError(error);
          outcome = "error";
        }
      } catch (err) {
        if (window.console && console.error) { console.error("Monetra: form error", err); }
        showToast("Something went wrong. Please check that your entry was saved.");
        outcome = "done";
      }

      if (outcome === "done") {
        closeForm();
      } else {
        formSubmitting = false;
        $("form-submit").disabled = false;
      }
    });

    $("form-dialog").addEventListener("close", function () {
      currentForm = null;
      formSubmitting = false;
    });
  }

  /* ---------------------------------------------------------
     18b. CONFIRMATION POPUP (used before every delete)
     --------------------------------------------------------- */
  var currentConfirm = null;

  function listHTML(items) {
    return "<ul>" + items.map(function (s) { return "<li>" + esc(s) + "</li>"; }).join("") + "</ul>";
  }

  function fillConfirmBox(id, title, items) {
    var box = $(id);
    if (items && items.length) {
      box.innerHTML = "<h3>" + esc(title) + "</h3>" + listHTML(items);
      box.hidden = false;
    } else {
      box.innerHTML = "";
      box.hidden = true;
    }
  }

  /* cfg: title, message, summary [[label, value]], removes [text], removesTitle,
          keeps [text], keepsTitle, note, field {label, options, value, hint, type, placeholder},
          confirmLabel, onConfirm(fieldValue) -> error text or nothing */
  function openConfirm(cfg) {
    currentConfirm = cfg;
    $("confirm-title").textContent = cfg.title;

    var msg = $("confirm-message");
    msg.textContent = cfg.message || "";
    msg.hidden = !cfg.message;

    var summary = $("confirm-summary");
    summary.innerHTML = (cfg.summary || []).map(function (row) {
      return "<div><dt>" + esc(row[0]) + "</dt><dd>" + esc(row[1]) + "</dd></div>";
    }).join("");
    summary.hidden = !(cfg.summary && cfg.summary.length);

    fillConfirmBox("confirm-removes", cfg.removesTitle || "Also removed", cfg.removes);
    fillConfirmBox("confirm-keeps", cfg.keepsTitle || "Stays safe", cfg.keeps);

    var fieldBox = $("confirm-field");
    if (cfg.field) {
      fieldBox.innerHTML = fieldHTML({
        name: "confirm-target", label: cfg.field.label, type: cfg.field.type || "select",
        value: cfg.field.value, options: cfg.field.options, hint: cfg.field.hint,
        placeholder: cfg.field.placeholder
      });
      fieldBox.hidden = false;
    } else {
      fieldBox.innerHTML = "";
      fieldBox.hidden = true;
    }

    var note = $("confirm-note");
    note.textContent = cfg.note || "";
    note.hidden = !cfg.note;
    $("confirm-error").hidden = true;
    $("confirm-ok").textContent = cfg.confirmLabel || "Delete";
    $("confirm-ok").className = "btn " + (cfg.confirmClass || "btn-danger");
    $("confirm-cancel").textContent = cfg.cancelLabel || "Cancel";

    var dialog = $("confirm-dialog");
    if (typeof dialog.showModal === "function") {
      if (!dialog.open) { dialog.showModal(); }
    } else {
      dialog.setAttribute("open", "");
    }
    // Cancel is focused first so Enter never deletes by accident
    setTimeout(function () {
      var first = cfg.field ? $("f-confirm-target") : $("confirm-cancel");
      if (first) { first.focus(); }
    }, 30);
  }

  function closeConfirm() {
    currentConfirm = null;
    var dialog = $("confirm-dialog");
    if (dialog.open) {
      if (typeof dialog.close === "function") { dialog.close(); } else { dialog.removeAttribute("open"); }
    }
  }

  function setupConfirmEvents() {
    $("confirm-form").addEventListener("submit", function (event) {
      event.preventDefault();
      if (!currentConfirm) { return; }
      var cfg = currentConfirm;
      currentConfirm = null;   // a second click on the button finds nothing to confirm
      var value = cfg.field && $("f-confirm-target") ? $("f-confirm-target").value : null;
      var error = null;
      try {
        error = cfg.onConfirm(value);
      } catch (err) {
        if (window.console && console.error) { console.error("Monetra: confirm error", err); }
        showToast("Something went wrong. Please check your records.");
        error = null;
      }
      if (error) {
        currentConfirm = cfg;
        var box = $("confirm-error");
        box.textContent = error;
        box.hidden = false;
        return;
      }
      closeConfirm();
    });

    $("confirm-dialog").addEventListener("close", function () {
      currentConfirm = null;
    });
  }

  var AMOUNT_HELP = "Please enter a valid amount, like 2500 or 2500.50.";

  /* ---- Income form ---- */
  // Optional "Repeat": the entry itself is saved as usual, then a rule starts at its next date after today.
  // The Repeat control is no longer shown in the forms, so v.repeat is empty and this does nothing.
  // The function stays so older code paths keep working.
  function addRuleFromEntry(type, v, amount) {
    if (["weekly", "monthly", "yearly"].indexOf(v.repeat) === -1) { return; }
    var anchor = +v.date.slice(8, 10);
    var today = todayStr();
    var next = nextOccurrence(v.date, v.repeat, anchor);
    var guard = 0;
    while (next <= today && guard++ < 400) { next = nextOccurrence(next, v.repeat, anchor); }
    var r = { id: uid(), type: type, amount: amount, frequency: v.repeat, nextDate: next, anchorDay: anchor, active: true, createdAt: Date.now() };
    if (type === "income") { r.source = v.source; } else { r.categoryId = v.categoryId; r.method = v.method; }
    data.recurring.push(r);
  }

  // Warns (never blocks) when a new expense looks like one a recurring rule covers
  function findDuplicatesForManualExpense(amount, categoryId, date) {
    var today = todayStr();
    var found = [];
    data.transactions.forEach(function (t) {
      if (t.type !== "expense" || !t.recurringId || t.amount !== amount || t.categoryId !== categoryId || t.date > today) { return; }
      var rule = findById(data.recurring, t.recurringId);
      if (sameIncomeWindow(rule ? rule.frequency : "", t.date, date)) {
        found.push(formatMoney(t.amount) + ", " + categoryName(t.categoryId) + ", " + formatDate(t.date) + " (added by a recurring rule)");
      }
    });
    data.recurring.forEach(function (r) {
      if (r.type !== "expense" || !r.active || r.amount !== amount || r.categoryId !== categoryId) { return; }
      if (sameIncomeWindow(r.frequency, r.nextDate, date)) {
        found.push("Recurring " + frequencyLabel(r.frequency).toLowerCase() + " expense, " + formatMoney(r.amount) + ", scheduled for " + formatDate(r.nextDate));
      }
    });
    return found;
  }

  function openIncomeForm(id) {
    var t = id ? findById(data.transactions, id) : null;
    if (id && !t) { return; }

    var sources = [];
    data.transactions.forEach(function (x) {
      if (x.type === "income" && x.source && sources.indexOf(x.source) === -1) { sources.push(x.source); }
    });

    openForm({
      title: t ? "Edit Income" : "Add Income",
      submitLabel: t ? "Save Changes" : "Add Income",
      fields: [
        { name: "amount", label: "Amount", type: "money", value: t ? centsToInput(t.amount) : "", hint: "In " + data.settings.currency },
        { name: "source", label: "Income source", type: "text", value: t ? t.source : "", placeholder: "For example: Salary", suggestions: sources, maxlength: 60 },
        { name: "date", label: "Date", type: "date", value: t ? t.date : todayStr(), max: todayStr() }
      ],
      onSubmit: function (v) {
        var amount = parseMoney(v.amount);
        if (amount === null) { return AMOUNT_HELP; }
        if (amount <= 0) { return "The amount must be more than 0."; }
        if (!v.source) { return "Please enter the income source, for example Salary."; }
        var dateError = checkDate(v.date, true);
        if (dateError) { return dateError; }

        function save() {
          var outsideNote = v.date < getPeriod(todayStr(), data.settings.monthStartDay).start
            ? " It is dated before this budget period, so it is not in This Month or Safe to Spend."
            : "";
          if (t) {
            t.amount = amount; t.source = v.source; t.date = v.date;
            commit("Income updated." + outsideNote);
          } else {
            data.transactions.push({
              id: uid(), type: "income", amount: amount, source: v.source,
              date: v.date, createdAt: Date.now()
            });
            commit("Income added." + outsideNote);
          }
        }

        // Check for a possible duplicate of a recurring income (new entries, or edits that
        // change the amount, source or date). An entry made by a rule is never checked against itself.
        var changed = !t || t.amount !== amount || t.source !== v.source || t.date !== v.date;
        if (changed && !(t && t.recurringId)) {
          var matches = findDuplicatesForManualIncome(amount, v.source, v.date, t ? t.id : null);
          if (matches.length) {
            askAboutDuplicateIncome({
              message: "This income looks like one that a recurring income already covers. " +
                "Saving it as well may count the same money twice.",
              summary: [
                ["Income source", v.source],
                ["Amount", formatMoney(amount)],
                ["Date", formatDate(v.date)]
              ],
              matchesTitle: "Similar recurring income",
              matches: matches,
              onConfirm: function () {
                closeForm();
                save();
              }
            });
            return FORM_PENDING;
          }
        }

        save();
        return null;
      }
    });
  }

  /* ---- Expense form ---- */
  function lastExpenseDefault(key) {
    var last = null;
    data.transactions.forEach(function (x) {
      if (x.type === "expense" && !x.billId && !x.debtId && x[key] && (!last || (x.createdAt || 0) > (last.createdAt || 0))) { last = x; }
    });
    if (key === "categoryId") { return last && getCategory(last.categoryId) ? last.categoryId : ""; }
    return last && last.method ? last.method : "Cash";
  }

  function openExpenseForm(id) {
    var t = id ? findById(data.transactions, id) : null;
    if (id && !t) { return; }
    if (data.categories.length === 0) {
      showToast("Please add a category first.");
      openCategoryForm();
      return;
    }

    openForm({
      title: t ? "Edit Expense" : "Add Expense",
      submitLabel: t ? "Save Changes" : "Add Expense",
      fields: [
        { name: "amount", label: "Amount", type: "money", value: t ? centsToInput(t.amount) : "", hint: "In " + data.settings.currency },
        { name: "categoryId", label: "Category", type: "select", value: t ? t.categoryId : lastExpenseDefault("categoryId"), options: categoryOptions(), addCategory: true },
        { name: "date", label: "Date", type: "date", value: t ? t.date : todayStr(), max: todayStr() },
        { name: "method", label: "Payment method", type: "select", value: t ? t.method : lastExpenseDefault("method"),
          options: PAYMENT_METHODS.map(function (m) { return { value: m, label: m }; }) }
      ],
      onSubmit: function (v) {
        var amount = parseMoney(v.amount);
        if (amount === null) { return AMOUNT_HELP; }
        if (amount <= 0) { return "The amount must be more than 0."; }
        if (!getCategory(v.categoryId)) { return "Please choose a category."; }
        var dateError = checkDate(v.date, true);
        if (dateError) { return dateError; }

        if (!t) {
          var dupes = findDuplicatesForManualExpense(amount, v.categoryId, v.date);
          if (dupes.length) {
            askAboutDuplicateIncome({
              title: "Possible duplicate expense",
              message: "This expense looks like one a recurring expense already covers. Saving it as well may count the same spending twice.",
              summary: [["Category", categoryName(v.categoryId)], ["Amount", formatMoney(amount)], ["Date", formatDate(v.date)]],
              matchesTitle: "Similar recurring expense",
              matches: dupes,
              onConfirm: function () {
                closeForm();
                data.transactions.push({ id: uid(), type: "expense", amount: amount, categoryId: v.categoryId, date: v.date, method: v.method, createdAt: Date.now() });
                commit("Expense added.");
              }
            });
            return FORM_PENDING;
          }
        }
        if (t) {
          t.amount = amount; t.categoryId = v.categoryId;
          t.date = v.date; t.method = v.method;
          commit("Expense updated.");
        } else {
          data.transactions.push({
            id: uid(), type: "expense", amount: amount, categoryId: v.categoryId,
            date: v.date, method: v.method, createdAt: Date.now()
          });
          commit("Expense added.");
        }
        return null;
      }
    });
  }

  /* ---- Recurring form (kept for existing rules) ---- */
  function openRecurringForm(type, id) {
    var r = id ? findById(data.recurring, id) : null;
    if (id && !r) { return; }
    var kind = r ? r.type : type;
    var isIncome = kind === "income";
    if (!isIncome && data.categories.length === 0) {
      showToast("Please add a category first.");
      openCategoryForm();
      return;
    }

    var today = todayStr();
    var fields = [
      { name: "amount", label: "Amount", type: "money", value: r ? centsToInput(r.amount) : "", hint: "In " + data.settings.currency }
    ];
    if (isIncome) {
      fields.push({ name: "source", label: "Income source", type: "text", value: r ? r.source : "", placeholder: "For example: Salary", maxlength: 60 });
    } else {
      fields.push({ name: "categoryId", label: "Category", type: "select", value: r ? r.categoryId : "", options: categoryOptions(), addCategory: true });
      fields.push({ name: "method", label: "Payment method", type: "select", value: r ? r.method : "Cash",
        options: PAYMENT_METHODS.map(function (m) { return { value: m, label: m }; }) });
    }
    fields.push({ name: "frequency", label: "Repeats", type: "select", value: r ? r.frequency : "monthly", options: FREQUENCIES });
    fields.push({ name: "nextDate", label: "Next date", type: "date",
      value: r && r.nextDate >= today ? r.nextDate : today, min: today,
      hint: "The next entry is added on this date. Earlier dates are not filled in." });

    openForm({
      title: (r ? "Edit Recurring " : "Add Recurring ") + (isIncome ? "Income" : "Expense"),
      submitLabel: r ? "Save Changes" : "Add Recurring",
      fields: fields,
      onSubmit: function (v) {
        var amount = parseMoney(v.amount);
        if (amount === null) { return AMOUNT_HELP; }
        if (amount <= 0) { return "The amount must be more than 0."; }
        if (isIncome && !v.source) { return "Please enter the income source, for example Salary."; }
        if (!isIncome && !getCategory(v.categoryId)) { return "Please choose a category."; }
        if (["weekly", "monthly", "yearly"].indexOf(v.frequency) === -1) { return "Please choose how often it repeats."; }
        var dateError = checkDate(v.nextDate, false);
        if (dateError) { return dateError; }
        if (v.nextDate < todayStr()) { return "Please choose today or a later date."; }

        var anchorDay = +v.nextDate.slice(8, 10);
        function save() {
          if (r) {
            r.amount = amount; r.frequency = v.frequency; r.nextDate = v.nextDate; r.anchorDay = anchorDay;
            if (isIncome) { r.source = v.source; } else { r.categoryId = v.categoryId; r.method = v.method; }
            commit("Recurring entry updated.");
          } else {
            var entry = {
              id: uid(), type: kind, amount: amount, frequency: v.frequency,
              nextDate: v.nextDate, anchorDay: anchorDay, active: true, createdAt: Date.now()
            };
            if (isIncome) { entry.source = v.source; } else { entry.categoryId = v.categoryId; entry.method = v.method; }
            data.recurring.push(entry);
            commit("Recurring entry added.");
          }
        }

        // Check for a manual income in the same period (new rules, or edits that change
        // the amount, source, repeat or date). Only incomes that have already happened count.
        var changed = !r || r.amount !== amount || r.source !== v.source ||
          r.frequency !== v.frequency || r.nextDate !== v.nextDate;
        if (isIncome && changed) {
          var matches = findDuplicatesForRecurringIncome(amount, v.source, v.frequency, v.nextDate);
          if (matches.length) {
            askAboutDuplicateIncome({
              message: "You already added income that looks like this one for the same period. " +
                "Saving this recurring income may count the same money twice.",
              summary: [
                ["Recurring income", v.source],
                ["Amount", formatMoney(amount)],
                ["Repeats", frequencyLabel(v.frequency)],
                ["Next date", formatDate(v.nextDate)]
              ],
              matchesTitle: "Similar income already recorded",
              matches: matches,
              onConfirm: function () {
                closeForm();
                save();
              }
            });
            return FORM_PENDING;
          }
        }

        save();
        return null;
      }
    });
  }

  function toggleRecurring(id) {
    var r = findById(data.recurring, id);
    if (!r) { return; }
    if (r.active) {
      r.active = false;
      commit("Recurring entry paused. Nothing will be added until you resume it.");
    } else {
      r.active = true;
      var today = todayStr();
      var guard = 0;
      // Skip dates missed while paused so old entries are not added in bulk
      while (r.nextDate < today && guard < 400) {
        r.nextDate = nextOccurrence(r.nextDate, r.frequency, r.anchorDay);
        guard++;
      }
      commit("Recurring entry resumed. Next date: " + formatDate(r.nextDate) + ".");
    }
  }

  /* ---- Budget form ---- */
  function openBudgetForm(id) {
    var b = id ? findById(data.budgets, id) : null;
    if (id && !b) { return; }
    if (data.categories.length === 0) {
      showToast("Please add a category first.");
      openCategoryForm();
      return;
    }

    var options;
    if (b) {
      options = [{ value: b.categoryId, label: categoryName(b.categoryId) }];
    } else {
      var used = data.budgets.map(function (x) { return x.categoryId; });
      options = categoryOptions().filter(function (o) { return used.indexOf(o.value) === -1; });
      if (options.length === 0) {
        showToast("Every category already has a budget. You can edit one instead, or add a new category.");
        return;
      }
    }

    openForm({
      title: b ? "Edit Budget" : "Add Budget",
      submitLabel: b ? "Save Changes" : "Add Budget",
      fields: [
        { name: "categoryId", label: "Category", type: "select", value: b ? b.categoryId : "", options: options, disabled: !!b, addCategory: !b },
        { name: "limit", label: "Monthly spending limit", type: "money", value: b ? centsToInput(b.limit) : "", hint: "In " + data.settings.currency }
      ],
      onSubmit: function (v) {
        var limit = parseMoney(v.limit);
        if (limit === null) { return AMOUNT_HELP; }
        if (limit <= 0) { return "The spending limit must be more than 0."; }
        if (b) {
          b.limit = limit;
          commit("Budget updated.");
        } else {
          if (!getCategory(v.categoryId)) { return "Please choose a category."; }
          // Only a real, saved budget for this exact category counts as "already exists"
          var duplicate = data.budgets.some(function (x) { return x.categoryId === v.categoryId; });
          if (duplicate) { return "This category already has a budget. Edit it instead."; }
          data.budgets.push({ id: uid(), categoryId: v.categoryId, limit: limit });
          commit("Budget added.");
        }
        return null;
      }
    });
  }

  /* ---- Bill form ---- */
  // The payment expense of a bill: found through the bill's linkedExpenseId, or (older data)
  // through the explicit billId on the expense. Never guessed from name, amount or date.
  function billPaymentTx(bill) {
    if (bill.linkedExpenseId) {
      var t = findById(data.transactions, bill.linkedExpenseId);
      if (t && t.billId === bill.id) { return t; }
    }
    for (var i = 0; i < data.transactions.length; i++) {
      if (data.transactions[i].billId === bill.id) { return data.transactions[i]; }
    }
    return null;
  }

  // Makes the bill and its single payment expense agree. Returns what was removed (for Undo).
  function syncBillExpense(bill, wantPaid) {
    var linked = billPaymentTx(bill);
    var result = { removed: null, created: false };

    if (wantPaid) {
      if (linked) {
        linked.amount = bill.amount;
        linked.categoryId = bill.categoryId;
      } else {
        linked = {
          id: uid(), type: "expense", amount: bill.amount, categoryId: bill.categoryId,
          date: todayStr(), method: "", billId: bill.id, createdAt: Date.now()
        };
        data.transactions.push(linked);
        result.created = true;
      }
      bill.linkedExpenseId = linked.id;
      bill.paid = true;
    } else {
      if (linked) {
        result.removed = removeById(data.transactions, linked.id);
      }
      bill.linkedExpenseId = null;
      bill.paid = false;
    }
    return result;
  }

  function openBillForm(id) {
    var b = id ? findById(data.bills, id) : null;
    if (id && !b) { return; }
    if (data.categories.length === 0) {
      showToast("Please add a category first.");
      openCategoryForm();
      return;
    }

    var defaultCategory = "";
    data.categories.forEach(function (c) { if (c.name === "Bills & Utilities") { defaultCategory = c.id; } });

    openForm({
      title: b ? "Edit Bill" : "Add Bill",
      submitLabel: b ? "Save Changes" : "Add Bill",
      fields: [
        { name: "name", label: "Bill name", type: "text", value: b ? b.name : "", placeholder: "For example: Electricity", maxlength: 60 },
        { name: "amount", label: "Amount", type: "money", value: b ? centsToInput(b.amount) : "", hint: "In " + data.settings.currency },
        { name: "dueDate", label: "Due date", type: "date", value: b ? b.dueDate : todayStr() },
        { name: "categoryId", label: "Category", type: "select", value: b ? b.categoryId : defaultCategory, options: categoryOptions(), addCategory: true },
        { name: "status", label: "Status", type: "select", value: b && b.paid ? "paid" : "unpaid",
          options: [{ value: "unpaid", label: "Unpaid" }, { value: "paid", label: "Paid" }],
          hint: "Marking a bill as paid adds one linked expense (dated today). Editing a paid bill keeps that expense in step." }
      ],
      onSubmit: function (v) {
        if (!v.name) { return "Please enter the bill name."; }
        var amount = parseMoney(v.amount);
        if (amount === null) { return AMOUNT_HELP; }
        if (amount <= 0) { return "The amount must be more than 0."; }
        var dateError = checkDate(v.dueDate, false);
        if (dateError) { return dateError; }
        if (!getCategory(v.categoryId)) { return "Please choose a category."; }

        var wantPaid = v.status === "paid";
        if (b) {
          b.name = v.name; b.amount = amount; b.dueDate = v.dueDate; b.categoryId = v.categoryId;
          syncBillExpense(b, wantPaid);
          commit("Bill updated.");
        } else {
          var bill = {
            id: uid(), name: v.name, amount: amount, dueDate: v.dueDate,
            categoryId: v.categoryId, paid: false, linkedExpenseId: null, createdAt: Date.now()
          };
          data.bills.push(bill);
          syncBillExpense(bill, wantPaid);
          commit("Bill added.");
        }
        return null;
      }
    });
  }

  /* ---- Debt forms ---- */
  function openDebtForm(id) {
    var d = id ? findById(data.debts, id) : null;
    if (id && !d) { return; }
    openForm({
      title: d ? "Edit Debt" : "Add Debt",
      submitLabel: d ? "Save Changes" : "Add Debt",
      fields: [
        { name: "name", label: "Debt name", type: "text", value: d ? d.name : "", placeholder: "For example: Credit card", maxlength: 60 },
        { name: "original", label: "Original amount", type: "money", value: d ? centsToInput(d.original) : "" },
        { name: "paidBefore", label: "Already paid", type: "money", value: d && d.paidBefore ? centsToInput(d.paidBefore) : "", optional: true,
          hint: "Optional. Money you paid before using Monetra. It is not added to your expenses." },
        { name: "interestRate", label: "Interest Rate", type: "percent", value: d && isValidRate(d.interestRate) ? String(d.interestRate) : "", optional: true,
          placeholder: "e.g. 5%", maxlength: 8,
          hint: "Optional. For your information only. It is not added to your balance." }
      ],
      onSubmit: function (v) {
        if (!v.name) { return "Please enter a debt name."; }
        var original = parseMoney(v.original);
        if (original === null) { return "Please enter a valid original amount."; }
        if (original <= 0) { return "The original amount must be more than 0."; }
        var before = parseMoney(v.paidBefore === "" ? "0" : v.paidBefore);
        if (before === null) { return "Please enter a valid amount already paid, or leave it empty."; }
        var rate = parseInterestRate(v.interestRate);
        if (rate === undefined) { return "Please enter a valid interest rate from 0 to 100 (for example 5 or 5.5), or leave it empty."; }
        var recorded = d ? debtPaidTotal(d, "") - (d.paidBefore || 0) : 0;
        if (before + recorded > original) {
          return "The amount paid cannot be more than the original debt" + (recorded ? " (payments you recorded add up to " + formatMoney(recorded) + ")" : "") + ".";
        }
        if (d) {
          d.name = v.name; d.original = original; d.paidBefore = before; d.interestRate = rate;
          commit("Debt updated.");
        } else {
          data.debts.push({ id: uid(), name: v.name, original: original, paidBefore: before, interestRate: rate, payments: [], createdAt: Date.now() });
          commit("Debt added.");
        }
        return null;
      }
    });
  }

  function openDebtPaymentForm(debtId, payId) {
    var d = findById(data.debts, debtId);
    if (!d) { return; }
    var p = payId ? findById(d.payments, payId) : null;
    if (payId && !p) { return; }
    var room = d.original - debtPaidTotal(d, p ? p.id : "");
    if (room <= 0) { showToast("This debt is already paid off."); return; }
    openForm({
      title: p ? "Edit Payment" : "Record Payment",
      submitLabel: p ? "Save Changes" : "Save Payment",
      fields: [
        { name: "amount", label: "Payment amount", type: "money", value: p ? centsToInput(p.amount) : "", hint: "Remaining balance: " + formatMoney(room) },
        { name: "date", label: "Date", type: "date", value: p ? p.date : todayStr(), max: todayStr() }
      ],
      onSubmit: function (v) {
        var amount = parseMoney(v.amount);
        if (amount === null) { return "Please enter a valid payment amount."; }
        if (amount <= 0) { return "The payment must be more than 0."; }
        if (amount > room) { return "That is more than the remaining balance (" + formatMoney(room) + ")."; }
        if (!isValidDate(v.date) || v.date > todayStr()) { return "Please choose a valid date that is not in the future."; }
        var tx = p ? debtTx(p) : null;
        var isNew = !p;
        if (p) { p.amount = amount; p.date = v.date; } else { p = { id: uid(), amount: amount, date: v.date }; d.payments.push(p); }
        if (tx) {
          tx.amount = amount; tx.date = v.date;
        } else {
          data.transactions.push({ id: uid(), type: "expense", amount: amount, categoryId: DEBT_CATEGORY, date: v.date, method: "",
            debtId: d.id, debtPaymentId: p.id, createdAt: Date.now() });
        }
        commit(isNew ? "Payment recorded." : "Payment updated.");
        return null;
      }
    });
  }

  function deleteDebtPayment(debtId, payId) {
    var d = findById(data.debts, debtId);
    var p = d ? findById(d.payments, payId) : null;
    if (!p) { return; }
    openConfirm({
      title: "Delete this payment?",
      message: "The payment is removed from " + quoted(d.name) + " and from your expenses, so your balance and totals update right away.",
      summary: [["Debt", d.name], ["Amount", formatMoney(p.amount)], ["Date", formatDate(p.date)]],
      removes: ["The linked expense of " + formatMoney(p.amount)],
      removesTitle: "Also removed",
      keeps: ["The debt and its other payments", "All your other income and expenses"],
      confirmLabel: "Delete payment",
      onConfirm: function () {
        var tx = debtTx(p);
        if (tx) { removeById(data.transactions, tx.id); }
        removeById(d.payments, p.id);
        commit("Payment deleted.");
      }
    });
  }

  function deleteDebt(id) {
    var d = findById(data.debts, id);
    if (!d) { return; }
    openConfirm({
      title: "Delete this debt?",
      message: "The debt and its payment history will be removed. Payments you already recorded stay in your expenses as Debt payments, so your totals do not change.",
      summary: [["Debt", d.name], ["Original", formatMoney(d.original)], ["Payments recorded", String(d.payments.length)]],
      removes: ["The debt " + quoted(d.name) + " and its payment history"],
      removesTitle: "Removes",
      keeps: ["Your recorded payments, kept as expenses", "All your other income and expenses"],
      confirmLabel: "Delete debt",
      onConfirm: function () {
        d.payments.forEach(function (p) {
          var tx = debtTx(p);
          if (tx) { tx.debtId = ""; tx.debtPaymentId = ""; }
        });
        removeById(data.debts, d.id);
        commit("Debt deleted.");
      }
    });
  }

  /* ---- Goal forms ---- */
  function openGoalForm(id) {
    var g = id ? findById(data.goals, id) : null;
    if (id && !g) { return; }

    openForm({
      title: g ? "Edit Savings Goal" : "Add Savings Goal",
      submitLabel: g ? "Save Changes" : "Add Goal",
      fields: [
        { name: "name", label: "Goal name", type: "text", value: g ? g.name : "", placeholder: "For example: Emergency fund", maxlength: 60 },
        { name: "target", label: "Target amount", type: "money", value: g ? centsToInput(g.target) : "" },
        { name: "saved", label: "Current saved amount", type: "money", value: g ? centsToInput(g.saved) : "0", hint: "Use 0 if you are just starting." },
        { name: "plan", label: "Monthly planned saving", type: "money", value: g && g.monthlyPlan ? centsToInput(g.monthlyPlan) : "",
          optional: true, hint: "Only this amount is set aside in Safe to Spend, not the whole target." }
      ],
      onSubmit: function (v) {
        if (!v.name) { return "Please enter a goal name."; }
        var target = parseMoney(v.target);
        if (target === null) { return "Please enter a valid target amount."; }
        if (target <= 0) { return "The target must be more than 0."; }
        var saved = parseMoney(v.saved === "" ? "0" : v.saved);
        if (saved === null) { return "Please enter a valid saved amount (0 is fine)."; }
        var plan = parseMoney(v.plan === "" ? "0" : v.plan);
        if (plan === null) { return "Please enter a valid planned amount, or leave it empty."; }

        if (g) {
          g.name = v.name; g.target = target; g.saved = saved; g.monthlyPlan = plan;
          commit("Goal updated.");
        } else {
          data.goals.push({
            id: uid(), name: v.name, target: target, saved: saved,
            monthlyPlan: plan, contributions: [], createdAt: Date.now()
          });
          commit("Goal added.");
        }
        return null;
      }
    });
  }

  function openContributionForm(goalId) {
    if (data.goals.length === 0) {
      showToast("Create a savings goal first.");
      openGoalForm();
      return;
    }

    openForm({
      title: "Add Savings",
      submitLabel: "Add Savings",
      fields: [
        { name: "goalId", label: "Goal", type: "select", value: goalId || data.goals[0].id,
          options: data.goals.map(function (g) { return { value: g.id, label: g.name }; }) },
        { name: "amount", label: "Amount saved", type: "money", value: "", hint: "In " + data.settings.currency },
        { name: "date", label: "Date", type: "date", value: todayStr(), max: todayStr() }
      ],
      onSubmit: function (v) {
        var goal = findById(data.goals, v.goalId);
        if (!goal) { return "Please choose a goal."; }
        var amount = parseMoney(v.amount);
        if (amount === null) { return AMOUNT_HELP; }
        if (amount <= 0) { return "The amount must be more than 0."; }
        var dateError = checkDate(v.date, true);
        if (dateError) { return dateError; }

        goal.saved += amount;
        goal.contributions.push({ id: uid(), goalId: goal.id, date: v.date, amount: amount });
        commit("Savings added to " + goal.name + ".");
        return null;
      }
    });
  }

  /* ---- Category form ---- */
  function openCategoryForm(id) {
    var c = id ? findById(data.categories, id) : null;
    if (id && !c) { return; }

    openForm({
      title: c ? "Edit Category" : "Add Category",
      submitLabel: c ? "Save Changes" : "Add Category",
      fields: [
        { name: "name", label: "Category name", type: "text", value: c ? c.name : "", placeholder: "For example: Pets", maxlength: 40 }
      ],
      onSubmit: function (v) {
        if (!v.name) { return "Please enter a category name."; }
        var duplicate = data.categories.some(function (x) {
          return x.name.toLowerCase() === v.name.toLowerCase() && (!c || x.id !== c.id);
        });
        if (duplicate) { return "You already have a category with this name."; }

        if (c) {
          c.name = v.name;
          commit("Category updated.");
        } else {
          data.categories.push({ id: uid(), name: v.name });
          commit("Category added.");
        }
        return null;
      }
    });
  }

  /* ---------------------------------------------------------
     19. DELETE (confirmation first, then Undo)
     ---------------------------------------------------------
     Every delete explains what else is removed and what stays safe.
     Records are linked only by explicit ids (billId, linkedExpenseId,
     recurringId, categoryId, goal contributions inside their goal),
     never by name, amount or date. */

  function sumAmounts(list) {
    var total = 0;
    list.forEach(function (x) { total += x.amount; });
    return total;
  }

  /* ---- Income and expenses ---- */
  function deleteTransaction(id) {
    var t = findById(data.transactions, id);
    if (!t) { return; }
    var isIncome = t.type === "income";
    var bill = t.billId ? findById(data.bills, t.billId) : null;
    var rule = t.recurringId ? findById(data.recurring, t.recurringId) : null;

    var summary = [["Type", isIncome ? "Income" : (bill ? "Expense (bill payment)" : "Expense")]];
    summary.push(isIncome ? ["Source", t.source || "Income"] : ["Category", categoryName(t.categoryId)]);
    if (bill) { summary.push(["Bill", bill.name]); }
    summary.push(["Amount", formatMoney(t.amount)]);
    summary.push(["Date", formatDate(t.date)]);

    var message;
    var changes = [];
    var keeps = ["All your other income and expenses"];
    if (bill) {
      message = "This expense is the recorded payment for the bill " + quoted(bill.name) +
        ". Deleting it will mark that bill as unpaid again. All other expenses stay unchanged.";
      changes.push("The bill " + quoted(bill.name) + " becomes Unpaid and counts as a bill still to pay");
      keeps.push("The bill itself");
    } else if (isIncome) {
      message = "Only this income record will be removed. Your expenses and other income stay unchanged.";
    } else {
      message = "Only this expense will be removed. Your other transactions stay unchanged.";
    }
    if (rule) {
      keeps.push("The recurring entry (" + (rule.active ? "still active" : "paused") + "). This date is not added again automatically");
    }

    openConfirm({
      title: isIncome ? "Delete this income?" : (bill ? "Delete this bill payment?" : "Delete this expense?"),
      message: message,
      summary: summary,
      removes: changes,
      removesTitle: "Also changed",
      keeps: keeps,
      note: "Totals, budgets, history and Safe to Spend update right away.",
      confirmLabel: bill ? "Delete payment" : "Delete",
      onConfirm: function () {
        var record = removeById(data.transactions, id);
        if (!record) { return; }
        var unpaidBill = null;
        if (bill && findById(data.bills, bill.id)) {
          bill.paid = false;
          bill.linkedExpenseId = null;
          unpaidBill = bill;
        }
        var text = unpaidBill
          ? "Payment deleted. The bill is unpaid again."
          : (isIncome ? "Income" : "Expense") + " deleted.";
        commit(text, function () {
          restoreAt(data.transactions, record);
          if (unpaidBill && findById(data.bills, unpaidBill.id)) {
            unpaidBill.paid = true;
            unpaidBill.linkedExpenseId = id;
          }
          commit("Restored.");
        });
      }
    });
  }

  /* ---- Delete all income ---- */
  // Always read from the real saved records, never from a stored total.
  function incomeRecords() {
    return data.transactions.filter(function (t) { return t.type === "income"; });
  }

  function deleteAllIncome() {
    var list = incomeRecords();
    if (list.length === 0) { showToast("There is no income to delete."); return; }

    var total = 0;
    list.forEach(function (t) { total += t.amount; });
    var fromRules = list.filter(function (t) { return t.recurringId; }).length;
    var activeRules = data.recurring.filter(function (r) { return r.type === "income" && r.active; }).length;

    var keeps = ["All your expenses", "Your bills, budgets, savings goals and debts"];
    if (activeRules) {
      keeps.push(plural(activeRules, "active recurring income rule") + ". Future dates will still be added");
    }

    openConfirm({
      title: "Delete all income?",
      message: "Every income record, in every month, will be removed" +
        (fromRules ? ", including " + plural(fromRules, "record") + " added by recurring rules" : "") +
        ". Your expenses and everything else stay unchanged.",
      summary: [["Income records to delete", String(list.length)], ["Total amount", formatMoney(total)]],
      removes: [],
      removesTitle: "Also changed",
      keeps: keeps,
      note: "Monthly Review, Home, totals and Safe to Spend update right away. Right after deleting, you can tap Undo.",
      confirmLabel: "Delete all income",
      onConfirm: function () {
        var removedRecords = [];
        var keptList = [];
        data.transactions.forEach(function (t, index) {
          if (t.type === "income") { removedRecords.push({ item: t, index: index }); } else { keptList.push(t); }
        });
        if (removedRecords.length === 0) { return; }
        data.transactions.length = 0;
        keptList.forEach(function (t) { data.transactions.push(t); });

        commit(plural(removedRecords.length, "income record") + " deleted.", function () {
          removedRecords.forEach(function (r) { restoreAt(data.transactions, r); });
          commit("Income restored.");
        });
      }
    });
  }

  /* ---- Delete all expenses ---- */
  // Debt payments belong to Debt Payoff and cannot be deleted one by one in Expenses either,
  // so they are the only expenses this action leaves in place.
  function expensesDeletableInBulk() {
    return data.transactions.filter(function (t) { return t.type === "expense" && !t.debtId; });
  }

  function deleteAllExpenses() {
    var list = expensesDeletableInBulk();
    if (list.length === 0) { showToast("There are no expenses to delete."); return; }

    var total = 0;
    var paidBills = 0;
    list.forEach(function (t) {
      total += t.amount;
      if (t.billId && findById(data.bills, t.billId)) { paidBills++; }
    });
    var debtPayments = data.transactions.filter(function (t) { return t.type === "expense" && t.debtId; }).length;

    var changes = [];
    if (paidBills) {
      changes.push(plural(paidBills, "paid bill") + " will become Unpaid again, because " + (paidBills === 1 ? "its payment record is" : "their payment records are") + " deleted. The bills themselves stay.");
    }
    var keeps = ["All your income", "Your bills, budgets, savings goals and debts"];
    if (debtPayments) {
      keeps.push(plural(debtPayments, "debt payment") + " recorded in Debt Payoff (manage these on the Debts page)");
    }

    openConfirm({
      title: "Delete all expenses?",
      message: "Every expense you have recorded, in every month, will be removed. Your income and everything else stays unchanged.",
      summary: [["Expenses to delete", String(list.length)], ["Total amount", formatMoney(total)]],
      removes: changes,
      removesTitle: "Also changed",
      keeps: keeps,
      note: "Totals, budgets, history and Safe to Spend update right away. Right after deleting, you can tap Undo.",
      confirmLabel: "Delete all expenses",
      onConfirm: function () {
        var removedRecords = [];
        var keptList = [];
        data.transactions.forEach(function (t, index) {
          if (t.type === "expense" && !t.debtId) { removedRecords.push({ item: t, index: index }); } else { keptList.push(t); }
        });
        if (removedRecords.length === 0) { return; }
        data.transactions.length = 0;
        keptList.forEach(function (t) { data.transactions.push(t); });

        // Same rule as deleting one bill payment: the bill stays and becomes unpaid again
        var billStates = [];
        removedRecords.forEach(function (r) {
          var bill = r.item.billId ? findById(data.bills, r.item.billId) : null;
          if (bill) {
            billStates.push({ bill: bill, paid: bill.paid, linkedExpenseId: bill.linkedExpenseId });
            bill.paid = false;
            bill.linkedExpenseId = null;
          }
        });

        commit(plural(removedRecords.length, "expense") + " deleted.", function () {
          removedRecords.forEach(function (r) { restoreAt(data.transactions, r); });
          billStates.forEach(function (st) {
            if (findById(data.bills, st.bill.id)) {
              st.bill.paid = st.paid;
              st.bill.linkedExpenseId = st.linkedExpenseId;
            }
          });
          commit("Expenses restored.");
        });
      }
    });
  }

  /* ---- Bills ---- */
  function deleteBill(id) {
    var bill = findById(data.bills, id);
    if (!bill) { return; }
    var linked = billPaymentTx(bill);

    var summary = [
      ["Bill", bill.name],
      ["Amount", formatMoney(bill.amount)],
      ["Due date", formatDate(bill.dueDate)],
      ["Status", bill.paid ? "Paid" : "Unpaid"],
      ["Category", categoryName(bill.categoryId)]
    ];
    var message;
    var removes = [];
    var keeps = [];
    if (linked) {
      message = "Deleting this bill will also remove its linked payment expense. Other expenses will remain unchanged.";
      removes.push("Payment expense: " + formatMoney(linked.amount) + ", " + formatDate(linked.date) +
        " (" + categoryName(linked.categoryId) + ")");
      keeps.push("All other expenses and income");
    } else if (bill.paid) {
      message = "This bill is marked as paid, but no linked payment expense was found. Only the bill will be removed. Your expenses stay unchanged.";
      keeps.push("All expenses and income");
    } else {
      message = "Only this bill will be removed. It is unpaid, so no expense is linked to it and your expenses stay unchanged.";
      keeps.push("All expenses and income");
    }
    keeps.push("Your budgets, savings goals and categories");

    openConfirm({
      title: "Delete this bill?",
      message: message,
      summary: summary,
      removes: removes,
      removesTitle: "Also removed",
      keeps: keeps,
      note: "Upcoming bills, budgets and Safe to Spend update right away.",
      confirmLabel: "Delete bill",
      onConfirm: function () {
        var billRec = removeById(data.bills, id);
        if (!billRec) { return; }
        // The payment is removed only because it carries this bill's id (created for this bill alone)
        var payRec = linked && linked.billId === id ? removeById(data.transactions, linked.id) : null;
        commit(payRec ? "Bill and its payment expense deleted." : "Bill deleted.", function () {
          restoreAt(data.bills, billRec);
          if (payRec) { restoreAt(data.transactions, payRec); }
          commit("Restored.");
        });
      }
    });
  }

  function toggleBill(id) {
    var bill = findById(data.bills, id);
    if (!bill) { return; }
    var nowPaid = !bill.paid;
    var result = syncBillExpense(bill, nowPaid);
    if (nowPaid) {
      commit("Bill marked as paid and added to your expenses.");
      return;
    }
    var removed = result.removed;
    commit(removed ? "Bill marked as unpaid. Its payment expense was removed." : "Bill marked as unpaid.", function () {
      if (!findById(data.bills, id) || bill.paid) { return; }
      if (removed) { restoreAt(data.transactions, removed); }
      bill.paid = true;
      bill.linkedExpenseId = removed ? removed.item.id : null;
      commit("Restored.");
    });
  }

  /* ---- Savings goals ---- */
  function deleteGoal(id) {
    var g = findById(data.goals, id);
    if (!g) { return; }
    var stats = computeStats();
    var count = g.contributions.length;
    var total = sumAmounts(g.contributions);
    var reserve = goalReserve(g, stats.period, stats.today);

    var removes = ["The goal " + quoted(g.name)];
    if (count) {
      removes.push(plural(count, "planned contribution record") + ", " + formatMoney(total) + " in total");
    }

    openConfirm({
      title: "Delete this savings goal?",
      message: "This goal and its planned contribution records will be removed. Your regular transactions will remain safe.",
      summary: [
        ["Goal", g.name],
        ["Target", formatMoney(g.target)],
        ["Saved so far", formatMoney(g.saved)],
        ["Monthly plan", g.monthlyPlan > 0 ? formatMoney(g.monthlyPlan) : "Not set"]
      ],
      removes: removes,
      removesTitle: "Also removed",
      keeps: ["All income and expense transactions", "Your bills, budgets and categories"],
      note: reserve > 0
        ? "Safe to Spend will stop setting aside " + formatMoney(reserve) + " for this goal this period."
        : "This goal is not holding back any Safe to Spend this period.",
      confirmLabel: "Delete goal",
      onConfirm: function () {
        var record = removeById(data.goals, id);
        if (!record) { return; }
        commit("Goal and its contributions deleted.", function () {
          restoreAt(data.goals, record);
          commit("Restored.");
        });
      }
    });
  }

  /* ---- Budgets ---- */
  function deleteBudget(id) {
    var b = findById(data.budgets, id);
    if (!b) { return; }
    var name = categoryName(b.categoryId);
    var stats = computeStats();
    var spentNow = 0;
    stats.budgets.forEach(function (x) { if (x.id === id) { spentNow = x.spent; } });
    var catExpenses = data.transactions.filter(function (t) {
      return t.type === "expense" && t.categoryId === b.categoryId;
    }).length;

    openConfirm({
      title: "Delete this budget?",
      message: "Your budget will be removed. Your actual income and expense records will remain safe.",
      summary: [
        ["Budget", name],
        ["Monthly limit", formatMoney(b.limit)],
        ["Spent this period", formatMoney(spentNow)]
      ],
      removes: ["The " + formatMoney(b.limit) + " monthly limit for " + name],
      removesTitle: "Removed",
      keeps: [
        catExpenses ? plural(catExpenses, "expense") + " in " + name + " stay in your history" : "All income and expense records",
        "The category " + quoted(name) + " itself",
        "Your other budgets"
      ],
      note: "A budget is a plan, not spending, so no transactions are added or changed.",
      confirmLabel: "Delete budget",
      onConfirm: function () {
        var record = removeById(data.budgets, id);
        if (!record) { return; }
        commit("Budget deleted.", function () {
          restoreAt(data.budgets, record);
          commit("Restored.");
        });
      }
    });
  }

  /* ---- Categories ---- */
  function deleteCategory(id) {
    var c = findById(data.categories, id);
    if (!c) { return; }
    if (c.name === "Other") { showToast("Other is the safe place for records, so it stays."); return; }

    var txs = data.transactions.filter(function (t) { return t.type === "expense" && t.categoryId === id; });
    var bills = data.bills.filter(function (b) { return b.categoryId === id; });
    var recs = data.recurring.filter(function (r) { return r.type === "expense" && r.categoryId === id; });
    var budgets = data.budgets.filter(function (b) { return b.categoryId === id; });
    var billPayments = txs.filter(function (t) { return t.billId; }).length;
    var used = txs.length + bills.length + recs.length + budgets.length > 0;

    // Not used anywhere: plain confirmation
    if (!used) {
      openConfirm({
        title: "Delete this category?",
        message: "This category is not used by any expense, bill, budget or recurring entry, so nothing else is affected.",
        summary: [["Category", c.name]],
        removes: ["The category " + quoted(c.name)],
        removesTitle: "Removed",
        keeps: ["All income and expense records", "Your bills, budgets, goals and recurring entries"],
        confirmLabel: "Delete category",
        onConfirm: function () {
          var record = removeById(data.categories, id);
          if (!record) { return; }
          commit("Category deleted.", function () {
            restoreAt(data.categories, record);
            commit("Restored.");
          });
        }
      });
      return;
    }

    // Used: records must move to another category first
    var others = categoryOptions().filter(function (o) { return o.value !== id; });
    if (others.length === 0) {
      showToast("Add another category first, so the records of this one have somewhere to move.");
      return;
    }

    var moves = [];
    if (txs.length) {
      moves.push(plural(txs.length, "expense") + (billPayments ? " (" + plural(billPayments, "bill payment") + " included)" : ""));
    }
    if (bills.length) { moves.push(plural(bills.length, "bill")); }
    if (recs.length) { moves.push(plural(recs.length, "recurring expense")); }
    if (budgets.length) {
      moves.push("The budget of " + formatMoney(budgets[0].limit) +
        " (if the category you choose already has a budget, that one is kept and this one is removed)");
    }

    openConfirm({
      title: "Delete " + quoted(c.name) + "?",
      message: "This category is in use, so it cannot be deleted until its records move to another category.",
      summary: [["Category", c.name]],
      field: {
        label: "Move its records to", options: others, value: others[0].value
      },
      removes: moves,
      removesTitle: "Will move to the category you choose",
      keeps: ["No expense, bill or recurring entry is deleted", "All income records"],
      note: "You can Undo this right after. The amounts and dates of your records do not change.",
      confirmLabel: "Move records and delete",
      onConfirm: function (targetId) {
        var target = getCategory(targetId);
        if (!target || target.id === id) { return "Please choose a category to move the records to."; }

        var moved = { tx: [], bills: [], rec: [], budgets: [] };
        data.transactions.forEach(function (t) {
          if (t.type === "expense" && t.categoryId === id) { t.categoryId = target.id; moved.tx.push(t.id); }
        });
        data.bills.forEach(function (b) {
          if (b.categoryId === id) { b.categoryId = target.id; moved.bills.push(b.id); }
        });
        data.recurring.forEach(function (r) {
          if (r.type === "expense" && r.categoryId === id) { r.categoryId = target.id; moved.rec.push(r.id); }
        });

        var removedBudgets = [];
        var targetHasBudget = data.budgets.some(function (b) { return b.categoryId === target.id; });
        if (targetHasBudget) {
          budgets.forEach(function (b) {
            var rec = removeById(data.budgets, b.id);
            if (rec) { removedBudgets.push(rec); }
          });
        } else {
          data.budgets.forEach(function (b) {
            if (b.categoryId === id) { b.categoryId = target.id; moved.budgets.push(b.id); }
          });
        }

        var catRecord = removeById(data.categories, id);
        commit("Category deleted. Its records moved to " + target.name + ".", function () {
          restoreAt(data.categories, catRecord);
          function back(list, ids) {
            ids.forEach(function (rid) {
              var item = findById(list, rid);
              if (item) { item.categoryId = id; }
            });
          }
          back(data.transactions, moved.tx);
          back(data.bills, moved.bills);
          back(data.recurring, moved.rec);
          back(data.budgets, moved.budgets);
          removedBudgets.forEach(function (rec) { restoreAt(data.budgets, rec); });
          commit("Restored.");
        });
        return null;
      }
    });
  }

  /* ---- Recurring entries ---- */
  function deleteRecurring(id) {
    var r = findById(data.recurring, id);
    if (!r) { return; }
    var isIncome = r.type === "income";
    // Entries this rule already added stay exactly as they are (their recurringId is kept)
    var generated = data.transactions.filter(function (t) { return t.recurringId === id; });

    openConfirm({
      title: "Delete this recurring entry?",
      message: "Deleting it stops all future entries. Entries it already added stay in your history.",
      summary: [
        ["Type", isIncome ? "Recurring income" : "Recurring expense"],
        [isIncome ? "Source" : "Category", isIncome ? r.source : categoryName(r.categoryId)],
        ["Amount", formatMoney(r.amount)],
        ["Repeats", frequencyLabel(r.frequency)],
        ["Status", r.active ? "Active, next " + formatDate(r.nextDate) : "Paused"]
      ],
      removes: ["The recurring rule. Nothing more is added automatically"],
      removesTitle: "Removed",
      keeps: [
        generated.length
          ? plural(generated.length, "entry") + " already added (" + formatMoney(sumAmounts(generated)) + " in total)"
          : "No entries have been added by it yet",
        "All other income and expenses"
      ],
      note: "Just need a break? Cancel and use Pause instead. Pausing keeps the rule.",
      confirmLabel: "Delete recurring entry",
      onConfirm: function () {
        var record = removeById(data.recurring, id);
        if (!record) { return; }
        commit("Recurring entry deleted. Entries already added were kept.", function () {
          restoreAt(data.recurring, record);
          commit("Restored.");
        });
      }
    });
  }

  /* ---------------------------------------------------------
     20. SETTINGS (Currency, Day Start, comfort switches)
     --------------------------------------------------------- */
  function setupSettings() {
    var daySelect = $("settings-day");
    var html = "";
    for (var i = 1; i <= 28; i++) {
      html += '<option value="' + i + '">Day ' + i + "</option>";
    }
    daySelect.innerHTML = html;

    var notifyBox = $("pref-notify");
    if (notifyBox) {
      if (typeof Notification === "undefined") {
        notifyBox.disabled = true;
        notifyBox.nextElementSibling.querySelector("small").textContent = "Not available in this browser. In-app reminders still work.";
      }
      notifyBox.addEventListener("change", function () {
        var box = this;
        if (!box.checked) { lsSet("monetra.notify", "0"); return; }
        Notification.requestPermission().then(function (p) {
          if (p === "granted") { lsSet("monetra.notify", "1"); showToast("Browser reminders are on while Monetra is open."); }
          else { box.checked = false; lsSet("monetra.notify", "0"); showToast("No permission given. In-app reminders still work."); }
        });
      });
    }

    [["pref-focus", "focusMode"], ["pref-large", "largeText"], ["pref-motion", "reducedMotion"]].forEach(function (p) {
      var box = $(p[0]);
      if (!box) { return; }
      box.addEventListener("change", function () {
        data.settings[p[1]] = this.checked;
        commit();
      });
    });

    $("settings-form").addEventListener("submit", function (event) {
      event.preventDefault();
      var currency = $("settings-currency").value;
      var day = parseInt($("settings-day").value, 10);
      if (CURRENCIES.indexOf(currency) === -1 || !(day >= 1 && day <= 28)) {
        showToast("Please check your settings and try again.");
        return;
      }
      if ($("settings-name")) { data.settings.name = $("settings-name").value.trim().slice(0, 40); }
      data.settings.currency = currency;
      data.settings.monthStartDay = day;
      commit("Settings saved.");
    });
  }

  /* ---------------------------------------------------------
     20b. FIRST-TIME SETUP and RESET ALL DATA
     --------------------------------------------------------- */
  function setupError(message) {
    var box = $("setup-error");
    box.textContent = message;
    box.hidden = false;
    return false;
  }

  // One rule decides everything: setup is needed until data.setupCompleted is true.
  // Brand-new data starts with false. Existing users' data is marked true when it is loaded.
  function needsSetup() {
    return !!data && data.setupCompleted !== true;
  }

  // Opens the Home (Dashboard) page, whatever page the address bar was on before
  function openDashboard() {
    try {
      if (window.location.hash !== "#home") {
        window.history.replaceState(null, "", "#home");
      }
    } catch (error) {
      window.location.hash = "home";
    }
    showPage("home");
    window.scrollTo(0, 0);
  }

  // Shows the setup screen only while needsSetup() is true
  function applySetupState() {
    var screen = $("setup-screen");
    var needs = needsSetup();
    var wasHidden = screen.hidden;
    document.body.classList.toggle("setup-active", needs);
    screen.hidden = !needs;
    if (!needs || !wasHidden) { return; }

    $("setup-currency").value = data.settings.currency;         // USD for new users
    $("setup-day").value = String(data.settings.monthStartDay); // day 1 for new users
    ["setup-name", "setup-income-amount", "setup-income-source", "setup-expense-amount"].forEach(function (id) {
      $(id).value = "";
    });
    $("setup-expense-category").innerHTML = categoryOptions().map(function (o) {
      return '<option value="' + esc(o.value) + '">' + esc(o.label) + "</option>";
    }).join("");
    $("setup-optional").open = false;
    $("setup-error").hidden = true;
    $("setup-storage-warning").hidden = storageWorks;
    window.scrollTo(0, 0);
    setTimeout(function () {
      if (needsSetup() && $("setup-name")) { $("setup-name").focus({ preventScroll: true }); }
    }, 50);
  }

  function completeSetup(withEntries) {
    if (!data || data.setupCompleted === true) { return; }

    var currency = $("setup-currency").value;
    var day = parseInt($("setup-day").value, 10);
    if (CURRENCIES.indexOf(currency) === -1 || !(day >= 1 && day <= 28)) {
      return setupError("Please check your currency and month start day.");
    }

    var incomeCents = null;
    var expenseCents = null;
    var source = "";
    var categoryId = "";
    if (withEntries) {
      var incomeText = $("setup-income-amount").value.trim();
      source = $("setup-income-source").value.trim();
      var expenseText = $("setup-expense-amount").value.trim();
      categoryId = $("setup-expense-category").value;

      if (incomeText !== "" || source !== "") {
        incomeCents = parseMoney(incomeText);
        if (incomeCents === null) { return setupError(AMOUNT_HELP); }
        if (incomeCents <= 0) { return setupError("The income amount must be more than 0."); }
        if (!source) { return setupError("Please enter the income source, or clear the income fields."); }
      }
      if (expenseText !== "") {
        expenseCents = parseMoney(expenseText);
        if (expenseCents === null) { return setupError(AMOUNT_HELP); }
        if (expenseCents <= 0) { return setupError("The expense amount must be more than 0."); }
        if (!getCategory(categoryId)) { return setupError("Please choose an expense category."); }
      }
    }

    // Everything is valid: apply (no sample data is ever added)
    data.settings.name = $("setup-name").value.trim().slice(0, 40);
    data.settings.currency = currency;      // symbol/formatting only, nothing converted
    data.settings.monthStartDay = day;
    var today = todayStr();
    if (incomeCents !== null) {
      data.transactions.push({ id: uid(), type: "income", amount: incomeCents, source: source, date: today, createdAt: Date.now() });
    }
    if (expenseCents !== null) {
      data.transactions.push({ id: uid(), type: "expense", amount: expenseCents, categoryId: categoryId, date: today, method: "Cash", createdAt: Date.now() });
    }
    data.setupCompleted = true;             // saved to Local Storage by commit() below

    $("setup-error").hidden = true;
    fillSettingsForm();
    commit("You're all set. Welcome to Monetra!");
    applySetupState();
    openDashboard();
  }

  function setupFirstRun() {
    // Reuse the Settings option lists so currencies are defined in one place
    $("setup-currency").innerHTML = $("settings-currency").innerHTML;
    $("setup-day").innerHTML = $("settings-day").innerHTML;
    $("setup-form").addEventListener("submit", function (event) {
      event.preventDefault();
      completeSetup(true);
    });
    applySetupState();
  }

  /* ---- Reset All Data (typed confirmation, cannot be undone) ---- */
  function resetAllData() {
    openConfirm({
      title: "Reset all data?",
      message: "This permanently erases everything stored in this browser for this app. It cannot be undone. " +
        "Resetting or clearing browser data can permanently remove locally stored information unless you have a backup.",
      summary: [
        ["Transactions", String(data.transactions.length)],
        ["Bills", String(data.bills.length)],
        ["Budgets", String(data.budgets.length)],
        ["Savings goals", String(data.goals.length)],
        ["Recurring entries", String(data.recurring.length)]
      ],
      removesTitle: "Permanently removed",
      removes: ["All income, expenses, bills, budgets, goals, recurring entries and categories", "Your settings (currency returns to USD, month start to day 1)"],
      keepsTitle: "Not affected",
      keeps: ["Backup files you downloaded earlier (you can restore one afterwards)"],
      note: "Tip: cancel and use Download Backup first if you might want this data again.",
      field: { label: "Type RESET to confirm", type: "text", value: "", placeholder: "RESET" },
      confirmLabel: "Reset all data",
      onConfirm: function (typed) {
        if (String(typed || "").trim().toUpperCase() !== "RESET") {
          return "Please type RESET to confirm.";
        }
        var fresh = createDefaultData();   // setupCompleted is false, so onboarding shows again
        data = normalizeData(fresh);
        hideToast();
        fillSettingsForm();
        commit("All data has been reset.");
        applySetupState();
        return null;
      }
    });
  }

  /* ---------------------------------------------------------
     21. DOWNLOADS: CSV EXPORT, BACKUP, RESTORE
     --------------------------------------------------------- */
  function downloadFile(content, mimeType, filename) {
    var blob = new Blob([content], { type: mimeType });
    var url = URL.createObjectURL(blob);
    var link = document.createElement("a");
    link.href = url;
    link.download = filename;
    document.body.appendChild(link);
    link.click();
    document.body.removeChild(link);
    setTimeout(function () { URL.revokeObjectURL(url); }, 1000);
  }

  function csvCell(value) {
    var s = String(value == null ? "" : value);
    // Stop spreadsheets from running text that starts like a formula
    if (/^[=+\-@\t\r]/.test(s)) {
      s = "'" + s;
    }
    if (/[",\r\n]/.test(s)) {
      s = '"' + s.replace(/"/g, '""') + '"';
    }
    return s;
  }

  function exportCSV() {
    if (data.transactions.length === 0) {
      showToast("There are no income or expense records to export yet.");
      return;
    }
    var rows = [["Date", "Type", "Category", "Amount", "Currency", "Payment method"]];
    data.transactions.slice().sort(function (a, b) {
      if (a.date !== b.date) { return a.date < b.date ? -1 : 1; }
      return (a.createdAt || 0) - (b.createdAt || 0);
    }).forEach(function (t) {
      rows.push([
        t.date,
        t.type === "income" ? "Income" : "Expense",
        t.type === "income" ? t.source : categoryName(t.categoryId),
        (t.amount / 100).toFixed(2),
        data.settings.currency,
        t.method || ""
      ]);
    });
    var csv = "\uFEFF" + rows.map(function (row) { return row.map(csvCell).join(","); }).join("\r\n");
    downloadFile(csv, "text/csv;charset=utf-8", "monetra-transactions-" + todayStr() + ".csv");
    showToast("CSV file downloaded.");
  }

  function exportBackup() {
    var payload = { app: "calm-budget", backupVersion: 1, exportedAt: new Date().toISOString(), data: data };
    downloadFile(JSON.stringify(payload, null, 2), "application/json", "monetra-backup-" + todayStr() + ".json");
    showToast("Backup downloaded. Keep the file somewhere safe.");
  }

  function validateBackup(parsed) {
    if (!isPlainObject(parsed) || (parsed.app !== "calm-budget" && parsed.app !== "monetra") || !isPlainObject(parsed.data)) { return null; }
    var d = parsed.data;
    if (typeof d.version !== "number" || d.version > DATA_VERSION) { return null; }

    var lists = ["categories", "transactions", "bills", "goals", "budgets", "recurring", "debts"];
    for (var i = 0; i < lists.length; i++) {
      if (d[lists[i]] !== undefined && !Array.isArray(d[lists[i]])) { return null; }
    }

    var ok = true;
    (d.categories || []).forEach(function (c) {
      if (!isPlainObject(c) || typeof c.id !== "string" || typeof c.name !== "string") { ok = false; }
    });
    (d.transactions || []).forEach(function (t) {
      if (!isPlainObject(t) || typeof t.id !== "string" || (t.type !== "income" && t.type !== "expense") ||
          !isInt(t.amount) || t.amount < 0 || !isValidDate(t.date)) { ok = false; }
    });
    (d.bills || []).forEach(function (b) {
      if (!isPlainObject(b) || typeof b.id !== "string" || typeof b.name !== "string" ||
          !isInt(b.amount) || !isValidDate(b.dueDate)) { ok = false; }
    });
    (d.debts || []).forEach(function (x) {
      if (!isPlainObject(x) || typeof x.id !== "string" || typeof x.name !== "string" || !isInt(x.original) || x.original <= 0) { ok = false; return; }
      if (x.payments !== undefined && !Array.isArray(x.payments)) { ok = false; return; }
      (x.payments || []).forEach(function (p) {
        if (!isPlainObject(p) || !isInt(p.amount) || p.amount <= 0 || !isValidDate(p.date)) { ok = false; }
      });
    });
    (d.goals || []).forEach(function (g) {
      if (!isPlainObject(g) || typeof g.id !== "string" || typeof g.name !== "string" ||
          !isInt(g.target) || !isInt(g.saved)) { ok = false; }
      if (isPlainObject(g) && Array.isArray(g.contributions)) {
        g.contributions.forEach(function (c) {
          if (!isPlainObject(c) || !isInt(c.amount) || !isValidDate(c.date)) { ok = false; }
        });
      }
    });
    (d.budgets || []).forEach(function (b) {
      if (!isPlainObject(b) || typeof b.id !== "string" || typeof b.categoryId !== "string" || !isInt(b.limit)) { ok = false; }
    });
    (d.recurring || []).forEach(function (r) {
      if (!isPlainObject(r) || typeof r.id !== "string" || (r.type !== "income" && r.type !== "expense") ||
          !isInt(r.amount) || !isValidDate(r.nextDate)) { ok = false; }
    });
    if (!ok) { return null; }
    d.setupCompleted = true;   // restoring a backup means setup is done
    return normalizeData(d);
  }

  function setupRestore() {
    var input = $("restore-file");
    input.addEventListener("change", function () {
      var file = input.files && input.files[0];
      input.value = "";
      if (!file) { return; }
      var reader = new FileReader();
      reader.onload = function () {
        var restored = null;
        try {
          restored = validateBackup(JSON.parse(String(reader.result)));
        } catch (error) {
          restored = null;
        }
        if (!restored) {
          showToast("This file is not a valid Monetra backup, so nothing was changed.");
          return;
        }
        if (!window.confirm("Restore this backup? It will replace ALL the data currently in this app. This cannot be undone.")) {
          return;
        }
        data = restored;
        hideToast();   // an Undo from before the restore must not touch the restored data
        fillSettingsForm();
        commit("Backup restored.");
      };
      reader.onerror = function () {
        showToast("The file could not be read. Nothing was changed.");
      };
      reader.readAsText(file);
    });
  }

  /* ---------------------------------------------------------
     22. NAVIGATION
     --------------------------------------------------------- */
  function getPageFromHash() {
    var name = window.location.hash.replace("#", "");
    return PAGES.indexOf(name) !== -1 ? name : DEFAULT_PAGE;
  }

  function showPage(pageName) {
    PAGES.forEach(function (name) {
      var section = $(name);
      if (section) { section.hidden = name !== pageName; }
    });
    var links = document.querySelectorAll("#main-nav a[data-page]");
    Array.prototype.forEach.call(links, function (link) {
      var isActive = link.getAttribute("data-page") === pageName;
      link.classList.toggle("active", isActive);
      if (isActive) { link.setAttribute("aria-current", "page"); } else { link.removeAttribute("aria-current"); }
    });
  }

  function goToTopOfPage(pageName) {
    window.scrollTo(0, 0);
    var heading = document.querySelector("#" + pageName + " h1");
    if (heading) {
      heading.setAttribute("tabindex", "-1");
      heading.focus({ preventScroll: true });
    }
  }

  function setupNavigation() {
    window.addEventListener("hashchange", function () {
      var page = getPageFromHash();
      showPage(page);
      goToTopOfPage(page);
    });

    $("main-nav").addEventListener("click", function (event) {
      var link = event.target.closest("a[data-page]");
      if (link && link.getAttribute("data-page") === getPageFromHash()) {
        event.preventDefault();
        window.scrollTo(0, 0);
      }
    });

    showPage(getPageFromHash());
  }

  /* ---------------------------------------------------------
     23. BUTTON CLICKS (every data-action button is handled here)
     --------------------------------------------------------- */
  function setupClicks() {
    document.addEventListener("click", function (event) {
      var el = event.target.closest("[data-action]");
      if (!el) { return; }
      var action = el.getAttribute("data-action");
      var id = el.getAttribute("data-id");

      switch (action) {
        case "add-income": openIncomeForm(); break;
        case "add-expense": openExpenseForm(); break;
        case "add-budget": openBudgetForm(); break;
        case "add-bill": openBillForm(); break;
        case "add-goal": openGoalForm(); break;
        case "add-saving": openContributionForm(); break;
        case "add-category": openCategoryForm(); break;
        case "add-recurring-income": openRecurringForm("income"); break;
        case "add-recurring-expense": openRecurringForm("expense"); break;
        case "edit-recurring": openRecurringForm(null, id); break;
        case "toggle-recurring": toggleRecurring(id); break;
        case "delete-recurring": deleteRecurring(id); break;
        case "edit-transaction": {
          var t = findById(data.transactions, id);
          if (t && t.type === "income") { openIncomeForm(id); } else if (t) { openExpenseForm(id); }
          break;
        }
        case "delete-transaction": deleteTransaction(id); break;
        case "delete-all-expenses": deleteAllExpenses(); break;
        case "delete-all-income": deleteAllIncome(); break;
        case "edit-budget": openBudgetForm(id); break;
        case "delete-budget": deleteBudget(id); break;
        case "edit-bill": openBillForm(id); break;
        case "delete-bill": deleteBill(id); break;
        case "toggle-bill": toggleBill(id); break;
        case "edit-goal": openGoalForm(id); break;
        case "delete-goal": deleteGoal(id); break;
        case "add-debt": openDebtForm(); break;
        case "edit-debt": openDebtForm(id); break;
        case "delete-debt": deleteDebt(id); break;
        case "pay-debt": openDebtPaymentForm(id); break;
        case "edit-debt-payment": openDebtPaymentForm(id, el.getAttribute("data-pid")); break;
        case "delete-debt-payment": deleteDebtPayment(id, el.getAttribute("data-pid")); break;
        case "contribute-goal": openContributionForm(id); break;
        case "edit-category": openCategoryForm(id); break;
        case "delete-category": deleteCategory(id); break;
        case "close-form": closeForm(); break;
        case "close-confirm": closeConfirm(); break;
        case "export-backup": exportBackup(); break;
        case "export-csv": exportCSV(); break;
        case "restore-backup": $("restore-file").click(); break;
        case "skip-setup": completeSetup(false); break;
        case "reset-all": resetAllData(); break;
        case "add-recurring":
          openForm({
            title: "Add Recurring",
            submitLabel: "Next",
            fields: [{ name: "kind", label: "What repeats?", type: "select", value: "expense", options: [{ value: "expense", label: "Expense" }, { value: "income", label: "Income" }] }],
            onSubmit: function (v) {
              setTimeout(function () { openRecurringForm(v.kind === "income" ? "income" : "expense"); }, 0);
              return null;
            }
          });
          break;
        case "dismiss-catchup": catchUpActive = false; renderAll(); break;
        case "inline-category": {
          var box = el.nextElementSibling;
          box.hidden = !box.hidden;
          if (!box.hidden) { box.querySelector("input").focus(); }
          break;
        }
        case "inline-category-save": saveInlineCategory(el); break;
        case "review-prev": reviewOffset -= 1; renderAll(); break;
        case "review-next": if (reviewOffset < 0) { reviewOffset += 1; renderAll(); } break;
        case "toggle-focus": data.settings.focusMode = !data.settings.focusMode; commit(); break;
        default: break;
      }
    });

    $("toast-undo").addEventListener("click", function () {
      if (undoAction) {
        var fn = undoAction;
        undoAction = null;
        fn();
      }
    });

    // One search box: results appear only while something is typed
    $("history-search").addEventListener("input", renderHistory);

    // When the app is opened again (maybe on a new day), refresh the numbers
    document.addEventListener("visibilitychange", function () {
      if (!document.hidden) { refreshDay(); }
    });

    // Another tab changed the saved data: load it, so this tab never saves an old copy over it
    window.addEventListener("storage", function (event) {
      if (event.key !== STORAGE_KEY || event.storageArea !== window.localStorage) { return; }
      var result = loadFromKey(STORAGE_KEY);
      if (result.status !== "ok") { return; }
      data = result.value;
      closeForm();
      closeConfirm();
      hideToast();
      fillSettingsForm();
      refreshDay();
      applySetupState();
    });
  }

  /* ---------------------------------------------------------
     24. START
     --------------------------------------------------------- */
  function init() {
    try {
      storageWorks = checkStorageWorks();

      if (!storageWorks) {
        data = normalizeData(createDefaultData());
        showBanner(
          "storage-banner",
          "Your browser is blocking storage, so your data will not be saved after you close this page."
        );
      } else {
        removeLegacyKeys();
        data = loadPersonalData();
      }

      processRecurring();
      if (storageWorks) {
        saveData();
      }

      if (storageWorks) {
        var prevOpen = lsGet("monetra.lastOpen");
        if (prevOpen && /^\d{4}-\d{2}-\d{2}$/.test(prevOpen) && data.setupCompleted && daysBetween(prevOpen, todayStr()) >= 3) { catchUpActive = true; }
        lsSet("monetra.lastOpen", todayStr());
      }

      setupSettings();
      fillSettingsForm();
      setupFormEvents();
      setupConfirmEvents();
      setupRestore();
      setupClicks();
      setupNavigation();
      setupFirstRun();   // decides: Setup screen for new users, Dashboard for returning users
      renderAll();

      if (migrationNotes.length) {
        showToast("Data check: " + migrationNotes.join(" ") + " No records were deleted.");
      }

      // If the app stays open past midnight, refresh the day-based numbers
      setInterval(function () {
        if (data && todayStr() !== lastRenderDay) { refreshDay(); }
      }, 60000);
    } finally {
      // The page was hidden by index.html until now. Always show it, even after an error.
      document.documentElement.classList.remove("booting");
    }
  }

  init();
})();
