// Exercise handlers emitted from the actual Ur demos. No synthetic ASTs or
// reimplemented game logic: each action goes through the compiled transaction.
import assert from 'node:assert/strict';
import { getRuntime } from '../public/browser-runtime.mjs';

const marker = (html, name) => {
  const match = html.match(new RegExp(name + '="(\\d+)"'));
  assert(match, `Missing ${name} in ${html}`);
  return Number(match[1]);
};
const buttons = (html) => [
  ...html.matchAll(/<button\b([^>]*)>([\s\S]*?)<\/button>/g),
];
const findButton = (html, label) => {
  const button = buttons(html).find(
    (match) => match[1].includes(`title="${label}"`) || match[2] === label,
  );
  assert(button, `Missing button: ${label}`);
  return marker(button[0], 'data-vrp-onclick');
};
const inputs = (html) => [
  ...html.matchAll(/<input\b[^>]*data-vrp-control="(\d+)"[^>]*>/g),
];
const dispatch = (id, event = {}) => getRuntime().dispatch(id, event);

export async function checkInteractions(name, html, patches) {
  if (!['tic-tac-toe', 'lights-out', 'task-board'].includes(name)) return;
  const slot = marker(html, 'data-vrp-slot');
  const updated = (id, initial) =>
    patches.findLast(([target]) => target === id)?.[1] ?? initial;
  const board = () => updated(slot, html);
  const click = (label) => dispatch(findButton(board(), label));

  if (name === 'tic-tac-toe') {
    assert.match(board(), /X to move/);
    await click('Square 1');
    assert.match(board(), /O to move/);
    // Even a queued event targeting an occupied cell must be ignored.
    await click('Square 1');
    assert.match(board(), /Moves: 1/);
    const reset = () => dispatch(findButton(html, 'New game'));
    const lines = [
      [1, 2, 3],
      [4, 5, 6],
      [7, 8, 9],
      [1, 4, 7],
      [2, 5, 8],
      [3, 6, 9],
      [1, 5, 9],
      [3, 5, 7],
    ];
    for (const line of lines) {
      await reset();
      const others = [1, 2, 3, 4, 5, 6, 7, 8, 9].filter(
        (cell) => !line.includes(cell),
      );
      for (const cell of [line[0], others[0], line[1], others[1], line[2]])
        await click(`Square ${cell}`);
      assert.match(board(), /X wins!/);
      await click(`Square ${others[2]}`);
      assert.match(board(), /Moves: 5/);
      await click('Undo move');
      assert.match(board(), /X to move/);
      assert.doesNotMatch(board(), /wins!/);
    }
    await reset();
    for (const cell of [1, 2, 3, 5, 4, 8]) await click(`Square ${cell}`);
    assert.match(board(), /O wins!/);
    await reset();
    for (const cell of [1, 2, 3, 5, 4, 6, 8, 7, 9])
      await click(`Square ${cell}`);
    assert.match(board(), /Draw\./);
    await click('Undo move');
    assert.match(board(), /X to move/);
    await reset();
    assert.match(board(), /Moves: 0/);
    console.log(
      'Tic-tac-toe: all eight winning lines, draw, occupied cells, game-over guard, undo, reset.',
    );
  }

  if (name === 'lights-out') {
    const lights = () =>
      buttons(board())
        .filter((button) => /title="Tile /.test(button[1]))
        .map((button) => button[2]);
    const initial = lights();
    await click('Tile 4');
    const changed = lights().flatMap((value, i) =>
      value === initial[i] ? [] : [i + 1],
    );
    assert.deepEqual(
      changed,
      [3, 4, 8],
      'A right-edge press must not wrap to the next row',
    );
    await click('Tile 4');
    assert.deepEqual(lights(), initial, 'Pressing the same tile twice cancels');
    await click('Restart level');
    assert.match(board(), /Moves: 0/);
    for (let level = 1; level <= 3; level++) {
      assert.match(board(), new RegExp(`Level ${level} / 3`));
      let steps = 0;
      while (!board().includes('You solved it!')) {
        assert(++steps <= 16, 'Following hints must solve each level');
        await click('Hint');
        const hint = board().match(/Try row (\d+), column (\d+)/);
        assert(hint, board());
        await click(`Tile ${(Number(hint[1]) - 1) * 4 + Number(hint[2])}`);
      }
      assert.match(board(), /Lights on: 0/);
      assert(lights().every((value) => value === 'off'));
      await click('Tile 1');
      assert.match(board(), /You solved it!/);
      await click('Next level');
    }
    assert.match(board(), /Level 1 /);
    console.log(
      'Lights Out: edge adjacency, cancelling presses, restart, all three levels solved through hints.',
    );
  }

  if (name === 'task-board') {
    const sections = [
      ...html.matchAll(/<section\b[^>]*>([\s\S]*?)<\/section>/g),
    ];
    assert.equal(sections.length, 3);
    const slots = sections.map((section) =>
      marker(section[1], 'data-vrp-slot'),
    );
    const column = (i) => updated(slots[i], sections[i][1]);
    const all = () => slots.map((_, i) => column(i)).join('\n');
    const card = (id) => {
      const match = [...all().matchAll(/<div\b[^>]*>[\s\S]*?<\/div>/g)].find(
        (match) => match[0].includes(`title="Save card ${id}"`),
      );
      assert(match, `Missing card ${id}`);
      return match[0];
    };
    const [draft, search] = inputs(html)
      .slice(0, 2)
      .map((match) => Number(match[1]));
    const add = () => dispatch(findButton(html, 'Add card'));
    const cardClick = (id, action) =>
      dispatch(findButton(card(id), `${action} card ${id}`));
    const edit = (id, value) =>
      dispatch(Number(inputs(card(id))[0][1]), { value });
    await add();
    assert.match(updated(slot, html), /Give the card a title/);
    await dispatch(draft, { value: 'Ship <&> λ' });
    await add();
    assert.match(column(0), /To do \(2\)/);
    assert.match(card(4), /Ship &lt;&amp;> &#955;/);
    const beforeTyping = patches.filter(([id]) => slots.includes(id)).length;
    await edit(4, 'A draft that survives moving');
    assert.equal(
      patches.filter(([id]) => slots.includes(id)).length,
      beforeTyping,
      'Typing into a card must not redraw its input and lose focus',
    );
    await cardClick(4, 'Move');
    assert.match(column(1), /Doing \(2\)/);
    assert.match(card(4), /value="A draft that survives moving"/);
    await edit(4, 'Renamed <b>card</b> λ');
    await cardClick(4, 'Save');
    assert.match(card(4), /Renamed &lt;b>card&lt;\/b> &#955;/);
    await dispatch(search, { value: 'RENAMED' });
    assert.match(column(0), /To do \(0\)/);
    assert.match(column(1), /Doing \(1\)/);
    assert.match(column(2), /Done \(0\)/);
    await cardClick(4, 'Move');
    assert.match(column(2), /Done \(1\)/);
    await cardClick(4, 'Move');
    assert.match(column(0), /To do \(1\)/);
    await edit(4, '');
    await cardClick(4, 'Save');
    assert.match(updated(slot, html), /Give the card a title/);
    assert.match(card(4), /Renamed &lt;b>card&lt;\/b> &#955;/);
    await dispatch(search, { value: 'no matching cards' });
    for (let i = 0; i < 3; i++) assert.match(column(i), /No cards here/);
    await dispatch(findButton(html, 'Clear search'));
    await cardClick(4, 'Delete');
    assert.doesNotMatch(all(), /title="Save card 4"/);
    for (const [i, heading] of ['To do', 'Doing', 'Done'].entries())
      assert(column(i).includes(`${heading} (1)`));
    console.log(
      'Task board: add, empty-title rejection, escaped text, persistent drafts, save, move, live search, delete.',
    );
  }
}
