// Local rendered-artifact check. Run with Playwright available in NODE_PATH.
const { chromium } = require('playwright');
const fs = require('fs');
const path = require('path');
const { pathToFileURL } = require('url');
const root = path.resolve(__dirname, '../../..');
const knowledge = JSON.parse(fs.readFileSync(path.join(root, 'labyrinth/knowledge.json'), 'utf8'));
const sota = JSON.parse(fs.readFileSync(path.join(root, 'labyrinth/sota.json'), 'utf8'));
const expected = {
  rows: sota.entries.length,
  nodes: knowledge.nodes.length,
  board: knowledge.nodes.filter(n => (n.kind === 'question' && n.status !== 'answered') ||
    n.kind === 'hunch' || n.kind === 'deadend' ||
    (n.kind === 'conjecture' && n.status !== 'refuted')).length
};

(async () => {
  const browser = await chromium.launch({ headless: true, channel: 'chrome' });
  try {
    const page = await browser.newPage({ viewport: { width: 1440, height: 1000 } });
    const errors = [];
    page.on('pageerror', error => errors.push(error.message));
    const dashboard = pathToFileURL(path.join(root, 'labyrinth/dashboard/index.html')).href;
    await page.goto(dashboard + '#sota', { waitUntil: 'networkidle', timeout: 30000 });
    const result = {
      title: await page.title(),
      sotaRows: await page.locator('#sota-body tbody tr').count(),
      sotaVisible: await page.locator('#sota').isVisible(),
      frontierTabVisible: await page.locator('#tab-frontier').isVisible(),
      orientation: await page.locator('#orientation').innerText(),
      firstResult: await page.locator('#sota-body tbody tr').first().innerText()
    };
    await page.screenshot({ path: path.join(root, 'labyrinth/evidence/dashboard-sota.png') });
    await page.locator('#tab-graph').click();
    await page.locator('#kg-wrap svg circle').first().waitFor({ state: 'attached', timeout: 10000 });
    result.graphCircles = await page.locator('#kg-wrap svg circle').count();
    await page.locator('#kg-wrap svg circle').evaluateAll(circles => {
      const selected = circles.find(circle => circle.__data__.id === 'th.rooted-structure');
      if (!selected) throw new Error('Central interior node is missing.');
      selected.dispatchEvent(new MouseEvent('click', { bubbles: true }));
    });
    const detail = await page.locator('#kg-detail').textContent();
    result.constitutiveFieldsVisible = ['Données reçues', 'Constitution', 'Lectures dérivées',
      'Portée constitutive', 'Revue constitutive'].every(label => detail.includes(label));
    result.receivedDerivedDistinctionVisible = detail.includes('seul sourceCursorExact') &&
      detail.includes('sourceStateExact, locatedStepExact, targetStateExact');
    await page.locator('#kg-detail').scrollIntoViewIfNeeded();
    await page.screenshot({ path: path.join(root, 'labyrinth/evidence/dashboard-graph.png') });
    await page.locator('#tab-board').click();
    result.boardCards = await page.locator('#boardcols .card').count();
    await page.screenshot({ path: path.join(root, 'labyrinth/evidence/dashboard-board.png') });
    result.pageErrors = errors;
    result.verified_at = new Date().toISOString();
    fs.writeFileSync(path.join(root, 'labyrinth/evidence/dashboard-qa.json'),
      JSON.stringify(result, null, 2) + '\n');
    console.log(JSON.stringify(result));
    if (result.sotaRows !== expected.rows || result.graphCircles !== expected.nodes ||
        result.boardCards !== expected.board || !result.sotaVisible || result.frontierTabVisible ||
        !result.constitutiveFieldsVisible || !result.receivedDerivedDistinctionVisible ||
        !result.orientation.includes('relations témoignées') ||
        !result.firstResult.includes('Correspondance exacte positions') || errors.length) {
      process.exitCode = 1;
    }
  } finally {
    await browser.close();
  }
})().catch(error => { console.error(error); process.exitCode = 1; });
