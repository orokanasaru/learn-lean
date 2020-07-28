import { InfoRecord } from '@bryangingechen/lean-client-js-browser';
import React, { useEffect, useState } from 'react';
import { leanColorize } from './colorize';
import { Position } from './position';
import { ToggleDoc } from './toggle-doc';

export interface GoalWidgetProps {
  goal: InfoRecord;
  position: Position;
}

export function GoalWidget({ goal, position }: GoalWidgetProps) {
  const [goalType, setGoalType] = useState(goal.type);
  const [goalState, setGoalState] = useState(goal.state);

  useEffect(() => {
    leanColorize(goal.type).then(setGoalType);
  }, [goal.type]);

  useEffect(() => {
    leanColorize(goal.state).then(setGoalState);
  }, [goal.state]);

  const tacticHeader = goal.text && (
    <div className='info-header doc-header'>
      {position.line}:{position.column}: tactic{' '}
      {
        <span
          className='code-block'
          style={{ fontWeight: 'normal', display: 'inline' }}
        >
          {goal.text}
        </span>
      }
    </div>
  );

  const docs = goal.doc && <ToggleDoc doc={goal.doc} />;

  const typeHeader = goal.type && (
    <div className='info-header'>
      {position.line}:{position.column}: type{' '}
      {goal['full-id'] && (
        <span>
          {' '}
          of{' '}
          <span
            className='code-block'
            style={{ fontWeight: 'normal', display: 'inline' }}
          >
            {goal['full-id']}
          </span>
        </span>
      )}
    </div>
  );

  const typeBody = goal.type &&
  !goal.text && ( // don't show type of tactics
      <div
        className='code-block'
        dangerouslySetInnerHTML={{
          __html: goalType + !goal.doc && '<br />',
        }}
      />
    );

  const goalStateHeader = goal.state && (
    <div className='info-header'>
      {position.line}:{position.column}: goal
    </div>
  );

  const goalStateBody = goal.state && (
    <div
      className='code-block'
      dangerouslySetInnerHTML={{ __html: goalState + '<br />' }}
    />
  );

  return (
    // put tactic state first so that there's less jumping around when the cursor moves
    <div>
      {goalStateHeader}
      {goalStateBody}
      {tacticHeader || typeHeader}
      {typeBody}
      {docs}
    </div>
  );
}
