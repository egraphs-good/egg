console.log("Starting!");

const runList = d3.select("#runs").selectAll("li");

const dateFormat = d3.timeFormat("%Y-%m-%d");
const timeFormat = d3.timeFormat("%H:%M:%S");
const datetimeFormat = d => `${dateFormat(d)} ${timeFormat(d)}`;

const DIR_REGEX = /(.+?)___(.+?)___((.+?)-(\d+)-g([0-9a-f]+)(-dirty)?)/;
const BASE_URL = `${window.location.protocol}//${window.location.host}/egg-nightlies/`;
const DATA_DIR = BASE_URL + "data/";
const REPO = "https://github.com/mwillsey/egg";

function get(path) {
  // console.log("Fetching", path);
  return d3
    .json(path, { cache: "force-cache" })
    .catch(err => console.warn("Failed to get", path, err));
}

function link(href, text) {
  return `<a target="_blank" href=${href}>${text}</a>`
}

async function updatePlot(runs) {
  // get the active data
  let active = [];
  await Promise.all(runs.map(r => r.load(10)));
  for (let run of runs) {
    for (let suite of run.suites) {
      for (let test of suite.tests) {
        active.push(test);
      }
    }
  }

  // set the dimensions and margins of the graph
  let margin = { top: 20, right: 20, bottom: 30, left: 50 };
  let width = 960 - margin.left - margin.right;
  let height = 500 - margin.top - margin.bottom;

  // set the ranges
  let x = d3.scaleTime().range([0, width]);
  let y = d3.scaleLinear().range([height, 0]);

  let svg = d3
    .select("#plot")
    .attr("width", width + margin.left + margin.right)
    .attr("height", height + margin.top + margin.bottom)
    .append("g")
    .attr("transform", `translate(${margin.left}, ${margin.top})`);

  // Scale the range of the data
  x.domain(d3.extent(active, t => t.run.date));
  y.domain([0, d3.max(active, t => t.avg_time())]);

  let byName = d3
    .nest()
    .key(d => d.data.name)
    .entries(active);

  // define the 1st line
  let valueline = d3
    .line()
    .x(t => x(t.run.date))
    .y(t => y(t.avg_time()))
    .curve(d3.curveMonotoneX);

  let groups = svg
    .selectAll("g.path-group")
    .data(byName)
    .join("g")
    .attr("class", "path-group");

  groups
    .selectAll("path")
    .data(d => [d.values])
    .join("path")
    .attr("class", "line")
    .attr("d", test => valueline(test));

  groups
    .selectAll(".dot")
    .data(d => d.values)
    .join("circle")
    .attr("class", "dot")
    .attr("cx", t => x(t.run.date))
    .attr("cy", t => y(t.avg_time()))
    .attr("r", 5);

  tippy("#plot .dot", {
    allowHTML: true,
    interactive: true,
    appendTo: document.body,
    content(node) {
      let t = node.__data__;
      return `
        <table>
        <tr><td>Date</td>   <td>${datetimeFormat(t.run.date)}</td></tr>
        <tr><td>Rev</td>    <td>${t.run.branch} @ ${link(t.run.url, t.run.shortrev)}</td></tr>
        <tr><td>Suite</td>  <td>${link(t.suite.url, t.suite.name)}</td></tr>
        <tr><td>Test</td>   <td>${t.data.name}</td></tr>
        <tr><td>n</td>      <td>${t.data.times.length}</td></tr>
        <tr><td>avg</td>    <td>${t.avg_time()}</td></tr>
        </table>
      `;
    }
  });


  // Add the X Axis
  svg
    .append("g")
    .attr("transform", `translate(0, ${height})`)
    .call(d3.axisBottom(x));

  // Add the Y Axis
  svg.append("g").call(d3.axisLeft(y));

  // svg
  //   .selectAll(".text")
  //   .data(data)
  //   .enter()
  //   .append("text") // Uses the enter().append() method
  //   .attr("class", "label") // Assign a class for styling
  //   .attr("x", d => x(d.run.date))
  //   .attr("y", d => y(d.data.times[0]))
  //   .attr("dy", "-5")
  //   .text(() => "label");

}

class Run {
  constructor(dirname) {
    let match = DIR_REGEX.exec(dirname);
    this.path = DATA_DIR + dirname + "/";
    this.name = dirname;
    this.date = new Date(match[1]);
    this.branch = match[2];
    this.describe = match[3];
    this.tag = match[4];
    this.commitsAhead = +match[5];
    this.rev = match[6];
    this.dirty = !!match[7];

    this.suites = null;
    this.url = `${REPO}/tree/${this.rev}`;
    this.shortrev = this.rev.slice(0,7)
  }

  async load(depth = 1) {
    let suites = await get(this.path);
    this.suites = await Promise.all(
      suites
        .filter(s => s.type == "directory")
        .map(async s => {
          let suite = new Suite(this, s.name);
          if (depth > 0) {
            await suite.load(depth - 1);
          }
          return suite;
        })
    );
    return this;
  }
}

class Suite {
  constructor(run, name) {
    this.run = run;
    this.name = name;
    this.path = run.path + name + "/";

    this.tests = null;
    this.url = `${REPO}/blob/${run.rev}/tests/${name}.rs`;
  }

  async load(depth = 0) {
    let tests = await get(this.path);
    this.tests = await Promise.all(
      tests
        .filter(t => t.type == "file")
        .map(async t => {
          let test = new Test(this.run, this, t.name);
          if (depth > 0) {
            await test.load();
          }
          return test;
        })
    );
    return this;
  }
}

class Test {
  constructor(run, suite, name) {
    this.run = run;
    this.suite = suite;
    this.name = name;
    this.path = suite.path + name;
    this.data = null;
  }

  async load() {
    this.data = await get(this.path);
  }

  avg_time() {
    var total = 0;
    for (let t of this.data.times) total += t;
    return total / this.data.times.length;
  }
}

async function fetchRuns() {
  let runsListing = await d3.json(DATA_DIR);
  console.log("Got the listing", runsListing);
  let runs = runsListing
    .filter(i => i.type == "directory")
    .map(i => new Run(i.name));
  console.log("Runs: ", runs);
  return runs;
}

let RUNS = null;

async function init() {
  let runs = await fetchRuns();
  RUNS = runs;

  runList
    .data(runs)
    .join("li")
    .text(run => `${run.branch} ${datetimeFormat(run.date)}`);

  updatePlot(runs);
}

init()
  .then(() => console.log("Successful init"))
  .catch(e => console.error("Failed init", e));
