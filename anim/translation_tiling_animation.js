/* Self-contained SVG renderer. Embedded by generate_translation_tiling_animation.py. */
function createTilingAnimation(svg, data, options = {}) {
  const ns = 'http://www.w3.org/2000/svg';
  const scene = svg.querySelector('#assembly');
  const scale = data.pixelScale;
  let count = String(options.count || 243), key = options.key || 'extra';
  let phase = 1, playing = false, period = options.period || 12;
  let startTime = 0;
  let model, state, tiles = [], faces = [], previousOrder = [];
  let notify = () => {};

  function dot(a, b) { return a[0]*b[0] + a[1]*b[1] + a[2]*b[2]; }
  function render() {
    for (const tile of tiles) {
      const point = tile.start.map((x, i) => x+phase*(tile.end[i]-x));
      const x = scale*dot(point, data.right), y = -scale*dot(point, data.up);
      tile.depth = dot(point, data.eye);
      const transform = 'matrix('+scale+' 0 0 '+scale+' '+x.toFixed(6)+' '+y.toFixed(6)+')';
      for (const face of tile.faces) face.node.setAttribute('transform', transform);

    }
    faces.sort((a, b) => (a.tile.depth+a.depth)-(b.tile.depth+b.depth) || a.serial-b.serial);
    if (faces.some((face, i) => face.serial !== previousOrder[i])) {
      scene.replaceChildren(...faces.map(face => face.node));
      previousOrder = faces.map(face => face.serial);
    }
    svg.dataset.spread = phase.toFixed(6);
    svg.dataset.tiles = count;
    svg.dataset.perturbation = key;
    notify(getState());
  }
  function setCase(nextCount, nextKey) {
    count = String(nextCount); key = nextKey;
    model = data.cases[count]; state = model.states[key];
    svg.querySelector('title').textContent=count+' translated crosses: assembly animation';
    svg.setAttribute('viewBox', state.fixedViewBox.map(x => x.toFixed(6)).join(' '));
    tiles = []; faces = []; previousOrder = [];
    scene.replaceChildren();
    for (let i = 0; i < model.centers.length; i++) {
      const tile = { start:model.centers[i], end:state.positions[i], faces:[], depth:0 };
      tiles.push(tile);
      for (let j = 0; j < data.polygons.length; j++) {
        const node = document.createElementNS(ns, 'g');
        node.innerHTML = data.polygons[j];
        const polygon = node.firstElementChild;
        polygon.setAttribute('fill', data.styles[model.colors[i]][j][0]);
        polygon.setAttribute('stroke', data.styles[model.colors[i]][j][1]);
        polygon.setAttribute('fill-opacity', data.opacity);
        polygon.setAttribute('stroke-opacity', Math.min(1, data.opacity+.13));
        polygon.setAttribute('data-tile', i);
        polygon.setAttribute('data-center', model.centers[i].join(','));
        const face = { node, tile, depth:data.localDepths[j], serial:i*data.polygons.length+j };
        tile.faces.push(face); faces.push(face);
      }
    }
    phase = 1; startTime = performance.now(); render();
  }
  function smooth(x) { return x*x*(3-2*x); }
  function cycle(q) {
    if (q < .10) return 1;
    if (q < .45) return 1-smooth((q-.10)/.35);
    if (q < .60) return 0;
    if (q < .95) return smooth((q-.60)/.35);
    return 1;
  }
  function inverseSmooth(value) {
    let lo=0, hi=1;
    for (let i=0; i<25; i++) {
      const mid=(lo+hi)/2;
      if (smooth(mid)<value) lo=mid; else hi=mid;
    }
    return (lo+hi)/2;
  }
  function play() {
    const offset = phase >= .999999 ? 0 : .10+.35*inverseSmooth(1-phase);
    startTime = performance.now()-offset*period*1000;
    playing = true; notify(getState());
  }
  function pause() { playing=false; notify(getState()); }
  function setPhase(value) { phase=Math.max(0, Math.min(1, value)); render(); }
  function setPeriod(value) { period=Number(value); if (playing) play(); }
  function getState() { return { count:Number(count), key, phase, playing, period }; }
  function onUpdate(callback) { notify=callback; notify(getState()); }
  let previousTime = -Infinity;
  function tick(time) {
    if (playing && time-previousTime >= 1000/30) {
      phase = cycle(((time-startTime)/(period*1000))%1);
      render(); previousTime=time;
    }
    requestAnimationFrame(tick);
  }
  setCase(count, key);
  requestAnimationFrame(tick);
  return { play, pause, setPhase, setCase, setPeriod, getState, onUpdate };
}
