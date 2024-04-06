
function send_paycheck(payments: int, id: int, amount: int): int

function yearly_bonus(year: int): int

function read(list: int, index: int): int

method Main(l_payments_in: int, l_ids_in: int, l_salaries_in: int, l_num_updates_in: int, r_payments_in: int, r_ids_in: int, r_salaries_in: int, r_num_updates_in: int)
  decreases *
 {
  assume((l_ids_in == r_ids_in) && ((l_salaries_in == r_salaries_in) && ((l_num_updates_in == r_num_updates_in) && (l_payments_in == r_payments_in))));
  var l_payments: int := l_payments_in;
  var l_ids: int := l_ids_in;
  var l_salaries: int := l_salaries_in;
  var l_num_updates: int := l_num_updates_in;
  var l_i: int := 0;
  var r_payments: int := r_payments_in;
  var r_ids: int := r_ids_in;
  var r_salaries: int := r_salaries_in;
  var r_num_updates: int := r_num_updates_in;
  var r_bonus: int := yearly_bonus(2024);
  var r_i: int := 0;
  while ((l_i < l_num_updates) && (r_i < r_num_updates))
    decreases *
    invariant l_payments == r_payments
    invariant l_payments <= r_payments
    invariant l_payments >= r_payments
    invariant l_ids == r_ids
    invariant l_ids <= r_ids
    invariant l_ids >= r_ids
    invariant l_salaries == r_salaries
    invariant l_salaries <= r_salaries
    invariant l_salaries >= r_salaries
    invariant l_num_updates == r_num_updates
    invariant l_num_updates <= r_num_updates
    invariant l_num_updates >= r_num_updates
    invariant l_i == r_i
    invariant l_i <= r_i
    invariant l_i >= r_i
    invariant l_i >= 0
  {
    var l_id: int := read(l_ids, l_i);
    var l_salary: int := read(l_salaries, l_i);
    var l_bonus: int := yearly_bonus(2024);
    l_payments := send_paycheck(l_payments, l_id, l_salary + l_bonus);
    l_i := (l_i + 1);
    var r_id: int := read(r_ids, r_i);
    var r_salary: int := read(r_salaries, r_i);
    r_payments := send_paycheck(r_payments, r_id, r_salary + r_bonus);
    r_i := (r_i + 1);
  }
  if (l_i < l_num_updates) {
    while (l_i < l_num_updates) {
      var l_id: int := read(l_ids, l_i);
      var l_salary: int := read(l_salaries, l_i);
      var l_bonus: int := yearly_bonus(2024);
      l_payments := send_paycheck(l_payments, l_id, l_salary + l_bonus);
      l_i := (l_i + 1);
    }
  }
  if (r_i < r_num_updates) {
    while (r_i < r_num_updates) {
      var r_id: int := read(r_ids, r_i);
      var r_salary: int := read(r_salaries, r_i);
      r_payments := send_paycheck(r_payments, r_id, r_salary + r_bonus);
      r_i := (r_i + 1);
    }
  }
  assert(l_payments == r_payments);
 }
